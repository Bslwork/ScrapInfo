"""
Fax number + email finder (v4)

The input sheet only needs website URLs. For every website the script crawls the
likely pages (contact, locations, about, sitemap...) and extracts
  * EMAIL addresses, ranked by priority (same-domain, contact-type addresses first)
  * FAX numbers, by reading the label that sits next to each phone-style number. It crawls EVERY
internal page it can reach (not just the first hit), so faxes that appear on other
pages/locations are collected too.

Install:  pip install pandas openpyxl requests beautifulsoup4 lxml
Optional (for JavaScript-built sites):
          pip install playwright && playwright install chromium
"""
import heapq
import html as htmllib
import json
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import unquote, urljoin, urlparse

import pandas as pd
import requests
import urllib3
from bs4 import BeautifulSoup

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ----------------------------------------------------------------- settings
INPUT_FILE = "Websites.xlsx"          # sheet with website URLs
OUTPUT_FILE = "Fax_Results.xlsx"
URL_COLUMN = None            # e.g. "Website" to force the column; None = auto-detect
DETAIL_EXTRA_COLUMNS = []    # e.g. ["Name", "ID"]: copied into the "All Fax Locations"/"All Emails" sheets

# Duplicate removal (applied to all three sheets before saving)
REMOVE_DUPLICATES = True
DEDUPE_BY = ["Email", "Fax Number"]   # Results sheet: rows with the same values in ALL these columns are merged
                                      # (use ["Email"] or ["Fax Number"] to merge on just one)

# Email priority: the best-ranked address becomes the "Email" column. Edit freely.
# An address on the same domain as the website always beats third-party addresses.
EMAIL_PRIORITY_PREFIXES = ["contact", "info", "hello", "office", "admin", "inquiries", "inquiry",
                           "general", "mail", "frontdesk", "reception", "service", "customerservice"]
EMAIL_SECONDARY_PREFIXES = ["appointments", "appointment", "referrals", "referral", "records",
                            "medicalrecords", "billing", "support", "sales", "help", "scheduling",
                            "intake", "enquiries", "team", "hr"]
EMAIL_AVOID_PREFIXES = ["noreply", "donotreply", "unsubscribe", "privacy", "webmaster", "abuse",
                        "postmaster", "mailer", "bounce", "notifications", "newsletter"]

MAX_PAGES_PER_SITE = 300     # safety cap: pages crawled per website (raise it for huge sites)
MAX_SECONDS_PER_SITE = 420   # safety cap: max time spent on one website
BROWSER_MAX_PAGES = 30       # cap for the (slow) Playwright pass
MAX_WORKERS = 6              # websites processed in parallel
REQUEST_TIMEOUT = 20
RETRIES = 2
DELAY_SECONDS = 0.3          # polite delay between pages of the same site
USE_BROWSER_FALLBACK = False # True = 2nd pass with Playwright for rows still "Not found"

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Accept-Language": "en-US,en;q=0.9",
}

# Pages most likely to hold a labeled number get crawled first.
LINK_KEYWORDS = {
    "contact": 10, "fax": 9, "location": 6, "office": 5, "directory": 5,
    "about": 4, "provider": 4, "staff": 3, "appointment": 3, "patient": 2,
    "support": 2, "find-us": 5, "reach": 4,
}
COMMON_PATHS = ["/contact", "/contact-us", "/contactus", "/about", "/about-us",
                "/locations", "/location", "/our-locations", "/directory"]
SKIP_EXT = (".pdf", ".jpg", ".jpeg", ".png", ".gif", ".svg", ".zip", ".doc",
            ".docx", ".xls", ".xlsx", ".mp4", ".mp3", ".webp", ".css", ".js")

# ------------------------------------------------------------ phone helpers
SEP = r"[\s.\-–—()/]*"
ANY_PHONE = re.compile(r"(?<!\d)(?:\+?1[\s.\-]*)?\(?\d{3}\)?[\s.\-–—]*\d{3}[\s.\-–—]*\d{4}(?!\d)")


def normalize_phone(value):
    digits = re.sub(r"\D", "", str(value or ""))
    if len(digits) == 11 and digits.startswith("1"):
        digits = digits[1:]
    return digits


def number_regex(digits):
    """Exact number, tolerating (), spaces, dots, dashes and an optional +1."""
    return re.compile(r"(?<!\d)(?:\+?1[\s.\-]*)?\(?" + SEP.join(digits) + r"(?!\d)")


# --------------------------------------------------------- label detection
FAX_W = r"fax|facsimile|telefax"
PHONE_W = (r"phone|telephone|tel|ph|call(?:\s+us)?|main|office|toll[\s-]*free|mobile|cell|"
           r"direct|voice|customer\s+service|appointments?|reception|scheduling")
TAIL = r"(?:\s*(?:number|no\.?|#|line))?[\s:.\-–—|)\]]*$"

ADJ_FAX = re.compile(r"(?<![a-z])(?:%s)%s" % (FAX_W, TAIL), re.I)
ADJ_PHONE = re.compile(r"(?<![a-z])(?:%s)%s" % (PHONE_W, TAIL), re.I)
DUAL = re.compile(
    r"(?:phone|tel|telephone)\s*(?:/|&|and|or|-)\s*fax%s|fax\s*(?:/|&|and|or|-)\s*(?:phone|tel|telephone)%s"
    % (TAIL, TAIL), re.I)
SINGLE = re.compile(r"(?<![A-Za-z])([FTP])\s*[:.]\s*$")
NEAR_FAX = re.compile(r"(?<![a-z])(?:fax|facsimile|telefax)(?![a-z])", re.I)
NEAR_PHONE = re.compile(
    r"(?<![a-z])(?:phone|telephone|tel|call|main line|toll[\s-]*free|customer service|office|mobile)(?![a-z])",
    re.I)
AFTER_LABEL = re.compile(r"^\s*[\(\[]\s*(fax|facsimile|phone|tel|telephone|main|office|mobile|cell)\b", re.I)


def label_votes(text, start, end):
    """
    Decide what the number at text[start:end] is, using ONLY the label that
    belongs to it (text between the previous/next phone number and this one).
    Returns (fax_weight, phone_weight).
    """
    before = text[max(0, start - 70):start]
    prev = None
    for pm in ANY_PHONE.finditer(before):
        prev = pm
    if prev:
        before = before[prev.end():]

    after = text[end:end + 30]
    nxt = ANY_PHONE.search(after)
    if nxt:
        after = after[:nxt.start()]

    if DUAL.search(before):
        return 3, 3
    if ADJ_FAX.search(before):
        return 5, 0
    if ADJ_PHONE.search(before):
        return 0, 5

    m = AFTER_LABEL.match(after)           # "555-123-4567 (Fax)"
    if m:
        return (4, 0) if m.group(1).lower() in ("fax", "facsimile") else (0, 4)

    m = SINGLE.search(before)              # "F: 555..." / "T: 555..."
    if m:
        return (3, 0) if m.group(1) == "F" else (0, 3)

    f = [x.start() for x in NEAR_FAX.finditer(before)]
    p = [x.start() for x in NEAR_PHONE.finditer(before)]
    if f and (not p or f[-1] > p[-1]):
        return 2, 0
    if p:
        return 0, 2
    return 0, 0


# ----------------------------------------------------------------- fetching
_local = threading.local()


def requests_fetch(url):
    """Return (html, final_url). Retries, SSL fallback, charset fix."""
    if not hasattr(_local, "session"):
        _local.session = requests.Session()
        _local.session.headers.update(HEADERS)
    s = _local.session
    verify, last = True, None
    for attempt in range(RETRIES + 1):
        try:
            r = s.get(url, timeout=REQUEST_TIMEOUT, verify=verify)
            if r.status_code in (429, 503) and attempt < RETRIES:
                time.sleep(2 * (attempt + 1))
                continue
            r.raise_for_status()
            ct = r.headers.get("Content-Type", "").lower()
            if ct and not any(k in ct for k in ("html", "xml", "text")):
                raise ValueError(f"Unsupported content type: {ct}")
            if not r.encoding or r.encoding.lower() == "iso-8859-1":
                r.encoding = r.apparent_encoding
            return r.text, r.url
        except requests.exceptions.SSLError as exc:
            verify, last = False, exc
        except Exception as exc:
            last = exc
            time.sleep(0.8)
    raise last


class BrowserFetcher:
    """Renders JavaScript pages (optional, used in the second pass)."""
    is_browser = True

    def __init__(self):
        from playwright.sync_api import sync_playwright
        self.pw = sync_playwright().start()
        self.browser = self.pw.chromium.launch()
        self.ctx = self.browser.new_context(user_agent=HEADERS["User-Agent"])

    def __call__(self, url):
        page = self.ctx.new_page()
        try:
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=30000)
            except Exception:
                pass
            page.wait_for_timeout(2500)
            return page.content(), page.url
        finally:
            page.close()

    def close(self):
        self.browser.close()
        self.pw.stop()


# ------------------------------------------------------------------ parsing
def _walk_json(node, out):
    if isinstance(node, dict):
        for k, v in node.items():
            kl = k.lower()
            if kl in ("telephone", "phone") and isinstance(v, (str, int)):
                out.append(("Phone", str(v)))
            elif kl in ("faxnumber", "fax") and isinstance(v, (str, int)):
                out.append(("Fax", str(v)))
            elif kl == "email" and isinstance(v, str):
                out.append(("Email", v))
            else:
                _walk_json(v, out)
    elif isinstance(node, list):
        for v in node:
            _walk_json(v, out)


def host_key(url):
    return urlparse(url).netloc.lower().removeprefix("www.")


EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@(?:[A-Za-z0-9\-]+\.)+[A-Za-z]{2,}")
OBF_RE = re.compile(
    r"([A-Za-z0-9._%+\-]+)\s*[\[\(\{]\s*at\s*[\]\)\}]\s*"
    r"((?:[A-Za-z0-9\-]+\s*(?:\.|[\[\(\{]\s*dot\s*[\]\)\}])\s*)+[A-Za-z]{2,})", re.I)
BAD_TLDS = {"png", "jpg", "jpeg", "gif", "svg", "webp", "css", "js", "ico", "woff", "woff2", "ttf", "pdf", "mp4"}
BAD_DOMAINS = ("example.com", "domain.com", "yourdomain.com", "email.com", "test.com",
               "sentry.io", "wixpress.com")


def clean_email(e):
    e = unquote(str(e)).strip().strip(".,;:<>()[]{}'\"").lower()
    if e.count("@") != 1 or ".." in e or len(e) > 100 or not EMAIL_RE.fullmatch(e):
        return ""
    dom = e.split("@")[1]
    if dom.rsplit(".", 1)[1] in BAD_TLDS or any(dom == b or dom.endswith("." + b) for b in BAD_DOMAINS):
        return ""
    return e


def decode_cfemail(h):
    """Decode Cloudflare 'email protection' hex strings."""
    try:
        key = int(h[:2], 16)
        return "".join(chr(int(h[i:i + 2], 16) ^ key) for i in range(2, len(h), 2))
    except Exception:
        return ""


def site_domain(website):
    parts = host_key(website).split(".")
    if len(parts) >= 3 and parts[-2] in ("co", "com", "org", "net", "gov", "edu", "ac") and len(parts[-1]) == 2:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def _prefix_match(lp, prefixes):
    return any(lp == p or (len(p) >= 5 and lp.startswith(p)) for p in prefixes)


def email_score(email, info, sdom):
    local, dom = email.split("@")
    lp = re.sub(r"[^a-z0-9]", "", local)
    same = dom == sdom or dom.endswith("." + sdom)
    score = info["w"] + min(len(info["pages"]), 3)       # mailto/protected link > plain text; repeated
    score += 5 if same else 0                            # belongs to the website's own domain
    if _prefix_match(lp, EMAIL_PRIORITY_PREFIXES):
        score += 4
    elif _prefix_match(lp, EMAIL_SECONDARY_PREFIXES):
        score += 2
    if _prefix_match(lp, EMAIL_AVOID_PREFIXES):
        score -= 8
    if any("contact" in u.lower() for u in info["pages"]):
        score += 2
    return score, same


def parse_page(html, url):
    """Return (visible_text, raw_text, links[(score, url)], {email: weight})."""
    try:
        soup = BeautifulSoup(html, "lxml")
    except Exception:
        soup = BeautifulSoup(html, "html.parser")

    # 1) structured data (JSON-LD) -> synthetic labeled text
    synthetic = []
    for sc in soup.find_all("script", type=re.compile("ld\\+json", re.I)):
        try:
            found = []
            _walk_json(json.loads(sc.string or sc.get_text() or ""), found)
            synthetic += [f" {kind}: {val} . " for kind, val in found]
        except Exception:
            pass

    emails = {}

    def add_email(e, w):
        e = clean_email(e)
        if e:
            emails[e] = max(emails.get(e, 0), w)

    for el in soup.find_all(attrs={"data-cfemail": True}):      # Cloudflare-protected emails
        dec = decode_cfemail(str(el.get("data-cfemail")))
        add_email(dec, 3)
        if dec:
            try:
                el.string = dec
            except Exception:
                pass

    # 2) microdata + tel:/fax: links -> make the label visible in the text
    for el in soup.find_all(attrs={"itemprop": True}):
        ip = str(el.get("itemprop")).lower()
        if "faxnumber" in ip:
            el.insert_before(soup.new_string(" Fax: "))
        elif "telephone" in ip:
            el.insert_before(soup.new_string(" Phone: "))
    for a in soup.find_all("a", href=True):
        h = a["href"].strip()
        low = h.lower()
        if low.startswith("mailto:"):
            for part in re.split(r"[,;]", unquote(h[7:]).split("?")[0]):
                add_email(part, 3)
        elif "email-protection#" in low:
            add_email(decode_cfemail(h.split("#", 1)[1]), 3)
        elif low.startswith(("tel:", "callto:")):
            num = h.split(":", 1)[1]
            if normalize_phone(num) not in normalize_phone(a.get_text()):
                a.append(soup.new_string(f" {num} "))
        elif low.startswith("fax:"):
            a.insert_before(soup.new_string(" Fax: "))
            if normalize_phone(h[4:]) not in normalize_phone(a.get_text()):
                a.append(soup.new_string(f" {h[4:]} "))

    # 3) links worth following
    links, base = [], host_key(url)
    for a in soup.find_all("a", href=True):
        href = urljoin(url, a["href"]).split("#")[0]
        p = urlparse(href)
        if p.scheme not in ("http", "https") or host_key(href) != base:
            continue
        if p.path.lower().endswith(SKIP_EXT):
            continue
        label = (a.get_text(" ", strip=True) + " " + href).lower()
        score = sum(w for k, w in LINK_KEYWORDS.items() if k in label)
        if len(p.query) > 80:            # skip tracking / calendar-trap URLs
            continue
        links.append((score or 1, href))

    raw = re.sub(r"<[^>]+>", " ", htmllib.unescape(html))   # also catches scripts/attributes
    for tag in soup(["script", "style", "noscript", "svg"]):
        tag.decompose()
    text = re.sub(r"\s+", " ", soup.get_text(" ", strip=True) + " " + " ".join(synthetic))
    for m in EMAIL_RE.finditer(text):
        add_email(m.group(), 1)
    for m in OBF_RE.finditer(text):                              # "name [at] site [dot] com"
        dom = re.sub(r"\s*[\[\(\{]\s*dot\s*[\]\)\}]\s*", ".", m.group(2))
        add_email(m.group(1) + "@" + re.sub(r"\s+", "", dom), 1)
    return text, re.sub(r"\s+", " ", raw), links, emails


def sitemap_urls(site_root, fetch, limit=500):
    """All page URLs listed in sitemap(s); follows sitemap indexes."""
    todo = [urljoin(site_root, "/sitemap.xml")]
    try:
        robots, _ = fetch(urljoin(site_root, "/robots.txt"))
        todo += re.findall(r"(?im)^\s*sitemap:\s*(\S+)", robots)
    except Exception:
        pass
    pages, seen_maps = [], set()
    while todo and len(seen_maps) < 8 and len(pages) < limit:
        sm = todo.pop(0)
        if sm in seen_maps:
            continue
        seen_maps.add(sm)
        try:
            xml, _ = fetch(sm)
        except Exception:
            continue
        for u in re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", xml):
            u = htmllib.unescape(u)
            if u.lower().endswith(".xml") or "sitemap" in u.lower().rsplit("/", 1)[-1]:
                todo.append(u)
            elif host_key(u) == host_key(site_root) and not u.lower().endswith(SKIP_EXT):
                pages.append(u)
    return pages[:limit]


# ----------------------------------------------------------- fax extraction
def clean_url(site):
    site = str(site or "").strip()
    if not site or site.lower() == "nan":
        return ""
    site = site.split()[0]
    if not site.lower().startswith(("http://", "https://")):
        site = "https://" + site
    return site


def pretty(d):
    return f"({d[:3]}) {d[3:6]}-{d[6:]}" if len(d) == 10 else d


def url_key(u):
    p = urlparse(u)
    return (host_key(u) + p.path.rstrip("/") + ("?" + p.query if p.query else "")).lower()


def process_site(website, fetch, max_pages=None):
    """Crawl every reachable internal page and collect ALL numbers labeled Fax."""
    max_pages = max_pages or MAX_PAGES_PER_SITE
    cands = {}      # digits -> {"fax","phone","ev": {page_url: snippet}, "pages": set()}
    emails = {}     # email -> {"w": best source weight, "pages": set()}
    heap, queued, counter = [], set(), 0
    crawled, ok_pages, err, seeded = 0, 0, "", False
    started = time.time()

    def push(score, u):
        nonlocal counter
        k = url_key(u)
        if k in queued:
            return
        queued.add(k)
        counter += 1
        heapq.heappush(heap, (-score, counter, u))

    def record(source, url, only_fax=False):
        per_page = {}
        for m in ANY_PHONE.finditer(source):
            f, p = label_votes(source, m.start(), m.end())
            if not (f or p) or (only_fax and f <= p):
                continue
            d = normalize_phone(m.group())
            if only_fax and url in cands.get(d, {}).get("pages", ()):
                continue                       # already counted from visible text
            old = per_page.get(d)
            if not old or max(f, p) > max(old[0], old[1]):
                per_page[d] = (f, p, source[max(0, m.start() - 90): m.end() + 60].strip())
        for d, (f, p, snip) in per_page.items():       # count once per page
            c = cands.setdefault(d, {"fax": 0, "phone": 0, "ev": {}, "pages": set()})
            c["fax"] += f
            c["phone"] += p
            c["pages"].add(url)
            if f >= p and len(c["ev"]) < 40:
                c["ev"][url] = snip

    push(100, website)
    while heap and crawled < max_pages and time.time() - started < MAX_SECONDS_PER_SITE:
        _, _, url = heapq.heappop(heap)
        crawled += 1
        try:
            html, final_url = fetch(url)
            text, raw, links, page_emails = parse_page(html, final_url)   # final_url keeps redirects/www correct
            ok_pages += 1
        except Exception as exc:
            if not err and ok_pages == 0:      # only report if nothing has loaded (guessed paths 404 normally)
                err = f"{type(exc).__name__}: {str(exc)[:150]}"
            if crawled == 1 and url.startswith("https://"):   # retry homepage over http
                queued.discard(url_key(url))
                push(100, "http://" + url[len("https://"):])
            continue

        if not seeded:
            seeded = True
            root = f"{urlparse(final_url).scheme}://{urlparse(final_url).netloc}"
            for path in COMMON_PATHS:
                push(5, root + path)
            if not getattr(fetch, "is_browser", False):
                for u in sitemap_urls(root, fetch):
                    label = u.lower()
                    push(sum(w for k, w in LINK_KEYWORDS.items() if k in label) or 2, u)

        for score, link in links:
            push(score, link)

        for e, w in page_emails.items():
            info = emails.setdefault(e, {"w": 0, "pages": set()})
            info["w"] = max(info["w"], w)
            info["pages"].add(url)
        record(text, url)
        record(raw, url, only_fax=True)        # numbers hidden in scripts/attributes
        time.sleep(DELAY_SECONDS)              # NOTE: no early stop - every page is read

    faxes = [(d, c) for d, c in cands.items() if c["fax"] >= c["phone"] and c["fax"] > 0]
    faxes.sort(key=lambda x: (-(x[1]["fax"] - x[1]["phone"]), -len(x[1]["pages"])))
    phones = [d for d, c in cands.items() if c["phone"] > c["fax"]]

    out = {"Pages checked": crawled, "Pages loaded": ok_pages, "Error": err if not ok_pages else "",
           "Crawl complete": "Yes" if not heap else f"No (cap reached, {len(heap)} pages left)",
           "Phone Numbers (reference)": ", ".join(pretty(d) for d in phones[:4]),
           "_details": [], "_email_details": []}

    sdom = site_domain(website)
    ranked = sorted(((e, i, *email_score(e, i, sdom)) for e, i in emails.items()),
                    key=lambda x: (-x[2], x[0]))          # (email, info, score, same)
    if ranked:
        e, i, sc, same = ranked[0]
        out.update({
            "Email": e, "Email Status": "Email found", "Email Count": len(ranked),
            "Email Confidence": "High" if same and sc >= 10 else "Medium" if same else "Low (other domain)",
            "Other Emails": "; ".join(f"{x[0]} [{len(x[1]['pages'])} page(s)]" for x in ranked[1:10]),
            "Email Found On": " | ".join(sorted(i["pages"], key=lambda u: "contact" not in u.lower())[:3]) +
                              (f" (+{len(i['pages']) - 3} more)" if len(i["pages"]) > 3 else ""),
        })
        for rank, (e, i, sc, same) in enumerate(ranked, 1):
            out["_email_details"].append({
                "Email": e, "Priority rank": rank, "Score": sc,
                "Same domain as website": "Yes" if same else "No",
                "Pages with this email": len(i["pages"]),
                "Example page URLs": " | ".join(sorted(i["pages"], key=lambda u: "contact" not in u.lower())[:5])})
    elif ok_pages == 0:
        out["Email Status"] = "Website unreachable"
    else:
        out["Email Status"] = "No email listed on website"

    if faxes:
        d, c = faxes[0]
        conf = ("High" if c["fax"] >= 5 and c["phone"] == 0
                else "Medium" if c["fax"] > c["phone"] else "Low (shared phone/fax line)")
        out.update({
            "Fax Number": pretty(d), "Fax Confidence": conf, "Fax Status": "Fax found",
            "Fax Count": len(faxes),
            "Other Fax Numbers": "; ".join(f"{pretty(x)} [{len(y['pages'])} page(s)]"
                                           for x, y in faxes[1:10]),
            "Fax Evidence": " || ".join(list(c["ev"].values())[:2])[:1000],
            "Fax Found On": " | ".join(sorted(c["pages"])[:3]) +
                            (f" (+{len(c['pages']) - 3} more)" if len(c["pages"]) > 3 else ""),
        })
        for d, c in faxes:
            for page, snip in c["ev"].items():
                out["_details"].append({
                    "Fax Number": pretty(d), "Fax score": c["fax"], "Phone score": c["phone"],
                    "Pages with this fax": len(c["pages"]), "Page URL": page, "Fax Evidence": snip})
    elif ok_pages == 0:
        out.update({"Fax Status": "Website unreachable", "Fax Evidence": "Could not load any page."})
    else:
        out.update({"Fax Status": "No fax listed on website",
                    "Fax Evidence": f"No number labeled Fax in {ok_pages} loaded page(s)."})
    return out


# --------------------------------------------------------------------- main
def pick_url_column(df):
    if URL_COLUMN:
        if URL_COLUMN not in df.columns:
            raise SystemExit(f"URL_COLUMN {URL_COLUMN!r} not found. Columns: {list(df.columns)}")
        return URL_COLUMN

    def looks_like_url(v):
        v = str(v).strip()
        return bool(v) and " " not in v and bool(re.search(r"^(https?://|www\.)|\.[a-z]{2,}(/|$)", v, re.I))

    def score(c):
        share = sum(looks_like_url(v) for v in df[c]) / max(len(df), 1)
        bonus = 0.5 if re.search("website|url|link|web|site", str(c), re.I) else 0
        return share + bonus * (share > 0.3)       # header only counts if the values look like URLs

    return max(df.columns, key=score)


COLUMNS = ["Email", "Email Confidence", "Email Status", "Email Count", "Other Emails", "Email Found On",
           "Fax Number", "Fax Confidence", "Fax Status", "Fax Count", "Other Fax Numbers",
           "Phone Numbers (reference)", "Fax Evidence", "Fax Found On",
           "Pages checked", "Pages loaded", "Crawl complete", "Error"]
RETRY = {"No fax listed on website", "Website unreachable"}
EMAIL_RETRY = {"No email listed on website", "Website unreachable"}
FAX_KEYS = ["Fax Number", "Fax Confidence", "Fax Status", "Fax Count", "Other Fax Numbers",
            "Fax Evidence", "Fax Found On", "_details"]
EMAIL_KEYS = ["Email", "Email Confidence", "Email Status", "Email Count", "Other Emails",
              "Email Found On", "_email_details"]


def merge_results(old, new):
    """Browser pass: take fax/email groups from the new result only where the old one found nothing."""
    out = dict(old)
    for keys, flag, found in ((FAX_KEYS, "Fax Status", "Fax found"), (EMAIL_KEYS, "Email Status", "Email found")):
        if new.get(flag) == found and old.get(flag) != found:
            for k in keys:
                out[k] = new.get(k, [] if k.startswith("_") else "")
    return out


def run_site(website_raw, fetch, max_pages=None):
    website = clean_url(website_raw)
    if not website:
        return {"Fax Status": "Invalid/missing URL", "Email Status": "Invalid/missing URL",
                "_details": [], "_email_details": []}
    try:
        return process_site(website, fetch, max_pages)
    except Exception as exc:
        return {"Fax Status": "Error", "Email Status": "Error",
                "Error": f"{type(exc).__name__}: {exc}", "_details": [], "_email_details": []}


# ------------------------------------------------------------- duplicate removal
def norm_key(col, value):
    """Comparable form of a value: faxes -> digits only, everything else -> lower-case text."""
    v = str(value or "").strip().lower()
    return re.sub(r"\D", "", v) if "fax" in col.lower() else v


def _more(sites, kept_site, limit=5):
    others = [w for w in dict.fromkeys(sites) if w and w != kept_site]
    return " | ".join(others[:limit]) + (f" (+{len(others) - limit} more)" if len(others) > limit else "")


def dedupe_results(out, url_col):
    """
    Keep ONE row per distinct (Email, Fax Number) pair. Lookup dict `seen` maps each key to the
    row that was kept; later rows with the same key are dropped (entire row).
    Rows with neither an email nor a fax are never merged with other websites' empty rows,
    only with repeats of the same website.
    """
    cols = [c for c in DEDUPE_BY if c in out.columns]
    seen, keep, removed, dup_sites = {}, [], {}, {}
    for idx, row in out.iterrows():
        vals = tuple(norm_key(c, row[c]) for c in cols)
        key = ("data", vals) if any(vals) else ("site", clean_url(row[url_col]).lower().rstrip("/"))
        if key in seen:
            k = seen[key]
            removed[k] = removed.get(k, 0) + 1
            dup_sites.setdefault(k, []).append(clean_url(row[url_col]))
        else:
            seen[key] = idx
            keep.append(idx)
    res = out.loc[keep].copy()
    res["Duplicates removed"] = [removed.get(i, 0) for i in res.index]
    res["Duplicate websites"] = [_more(dup_sites.get(i, []), clean_url(res.at[i, url_col])) for i in res.index]
    return res.reset_index(drop=True), len(out) - len(res)


def dedupe_details(df, key_col, best_col):
    """One row per distinct value of key_col (across ALL websites); keeps the row with the highest best_col."""
    if df.empty:
        return df, 0
    d = df.reset_index(drop=True).copy()
    d["_order"] = range(len(d))
    d["_k"] = d[key_col].map(lambda v: norm_key(key_col, v))
    d["_best"] = pd.to_numeric(d[best_col], errors="coerce").fillna(0)
    d = d.sort_values("_best", ascending=False, kind="stable")          # best row first within each key
    rows = []
    for _, g in d.groupby("_k", sort=False):
        best = g.iloc[0].copy()
        best["Duplicates removed"] = len(g) - 1
        best["Also found on websites"] = _more(list(g.iloc[1:]["Website"]), best["Website"])
        best["_order"] = g["_order"].min()                              # keep original ordering
        rows.append(best)
    res = pd.DataFrame(rows).sort_values("_order").drop(columns=["_k", "_best", "_order"])
    return res.reset_index(drop=True), len(df) - len(res)


def main():
    df = pd.read_excel(INPUT_FILE, dtype=str, keep_default_na=False)
    url_col = pick_url_column(df)
    print(f"Using URL column: {url_col!r}  ({len(df)} rows)")

    unique = list(dict.fromkeys(clean_url(v) for v in df[url_col]))   # crawl each site once
    results = {}
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futs = {pool.submit(run_site, u, requests_fetch): u for u in unique}
        for n, fut in enumerate(as_completed(futs), 1):
            u = futs[fut]
            r = results[u] = fut.result()
            print(f"{n}/{len(unique)}: {u} -> email: {r.get('Email') or r['Email Status']} | "
                  f"fax: {r.get('Fax Number') or r['Fax Status']} "
                  f"({r.get('Email Count', 0)} emails, {r.get('Fax Count', 0)} faxes, {r.get('Pages checked', 0)} pages)")

    if USE_BROWSER_FALLBACK:
        todo = [u for u, r in results.items()
                if u and (r.get("Fax Status") in RETRY or r.get("Email Status") in EMAIL_RETRY)]
        if todo:
            print(f"\nBrowser pass for {len(todo)} sites...")
            browser = BrowserFetcher()
            try:
                for n, u in enumerate(todo, 1):
                    r = run_site(u, browser, BROWSER_MAX_PAGES)
                    results[u] = merge_results(results[u], r)
                    print(f"  {n}/{len(todo)}: {u} -> email: {r.get('Email') or r['Email Status']} | "
                          f"fax: {r.get('Fax Number') or r['Fax Status']}")
            finally:
                browser.close()

    res = pd.DataFrame([results[clean_url(v)] for v in df[url_col]]).reindex(columns=COLUMNS).fillna("")
    orig = df.reset_index(drop=True).copy()
    orig.columns = [f"{c} (input)" if c in COLUMNS else c for c in orig.columns]   # avoid name clashes
    out = pd.concat([orig, res], axis=1)                  # every original column is kept, in order

    extra = [c for c in DETAIL_EXTRA_COLUMNS if c in df.columns]
    first_row = {clean_url(r[url_col]): r for _, r in df.iloc[::-1].iterrows()}   # first row per website

    def make_details(key, cols):
        rows = [{"Website": u, **{c: first_row[u][c] for c in extra}, **d}
                for u, r in results.items() for d in r.get(key, [])]
        return pd.DataFrame(rows, columns=["Website", *extra, *cols])

    emails_df = make_details("_email_details", ["Email", "Priority rank", "Score", "Same domain as website",
                                                "Pages with this email", "Example page URLs"])
    faxes_df = make_details("_details", ["Fax Number", "Fax score", "Phone score", "Pages with this fax",
                                         "Page URL", "Fax Evidence"])
    if REMOVE_DUPLICATES:
        out, n1 = dedupe_results(out, url_col)
        emails_df, n2 = dedupe_details(emails_df, "Email", "Score")
        faxes_df, n3 = dedupe_details(faxes_df, "Fax Number", "Fax score")
        print(f"\nDuplicates removed -> Results: {n1} | All Emails: {n2} | All Fax Locations: {n3}")

    with pd.ExcelWriter(OUTPUT_FILE) as xw:
        out.to_excel(xw, sheet_name="Results", index=False)
        emails_df.to_excel(xw, sheet_name="All Emails", index=False)
        faxes_df.to_excel(xw, sheet_name="All Fax Locations", index=False)
    print("\nEmail status:\n", out["Email Status"].value_counts().to_string())
    print("\nFax status:\n", out["Fax Status"].value_counts().to_string())
    print(f"\nFinished. Results saved to: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
