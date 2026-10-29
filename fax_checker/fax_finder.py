"""
Fax number finder (v3)

The input sheet only needs website URLs. For every website the script crawls the
likely pages (contact, locations, about, sitemap...) and extracts the FAX number
by reading the label that sits next to each phone-style number. It crawls EVERY
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
from urllib.parse import urljoin, urlparse

import pandas as pd
import requests
import urllib3
from bs4 import BeautifulSoup

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ----------------------------------------------------------------- settings
INPUT_FILE = "Websites.xlsx"          # sheet with website URLs
OUTPUT_FILE = "Fax_Results.xlsx"

MAX_PAGES_PER_SITE = 300     # safety cap: pages crawled per website (raise it for huge sites)
MAX_SECONDS_PER_SITE = 420   # safety cap: max time spent on one website
BROWSER_MAX_PAGES = 30       # cap for the (slow) Playwright pass
MAX_WORKERS = 6              # websites processed in parallel
REQUEST_TIMEOUT = 20
RETRIES = 2
DELAY_SECONDS = 0.3          # polite delay between pages of the same site
USE_BROWSER_FALLBACK = True # True = 2nd pass with Playwright for rows still "Not found"

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
            else:
                _walk_json(v, out)
    elif isinstance(node, list):
        for v in node:
            _walk_json(v, out)


def host_key(url):
    return urlparse(url).netloc.lower().removeprefix("www.")


def parse_page(html, url):
    """Return (visible_text, raw_text, links[(score, url)])."""
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
        if low.startswith(("tel:", "callto:")):
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
    text = soup.get_text(" ", strip=True) + " " + " ".join(synthetic)
    return re.sub(r"\s+", " ", text), re.sub(r"\s+", " ", raw), links


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
            text, raw, links = parse_page(html, final_url)   # final_url keeps redirects/www correct
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

        record(text, url)
        record(raw, url, only_fax=True)        # numbers hidden in scripts/attributes
        time.sleep(DELAY_SECONDS)              # NOTE: no early stop - every page is read

    faxes = [(d, c) for d, c in cands.items() if c["fax"] >= c["phone"] and c["fax"] > 0]
    faxes.sort(key=lambda x: (-(x[1]["fax"] - x[1]["phone"]), -len(x[1]["pages"])))
    phones = [d for d, c in cands.items() if c["phone"] > c["fax"]]

    out = {"Pages checked": crawled, "Pages loaded": ok_pages, "Error": err if not ok_pages else "",
           "Crawl complete": "Yes" if not heap else f"No (cap reached, {len(heap)} pages left)",
           "Phone Numbers (reference)": ", ".join(pretty(d) for d in phones[:4]),
           "_details": []}
    if faxes:
        d, c = faxes[0]
        conf = ("High" if c["fax"] >= 5 and c["phone"] == 0
                else "Medium" if c["fax"] > c["phone"] else "Low (shared phone/fax line)")
        out.update({
            "Fax Number": pretty(d), "Fax Confidence": conf, "Status": "Fax found",
            "Fax Count": len(faxes),
            "Other Fax Numbers": "; ".join(f"{pretty(x)} [{len(y['pages'])} page(s)]"
                                           for x, y in faxes[1:10]),
            "Evidence": " || ".join(list(c["ev"].values())[:2])[:1000],
            "Fax Found On": " | ".join(sorted(c["pages"])[:3]) +
                            (f" (+{len(c['pages']) - 3} more)" if len(c["pages"]) > 3 else ""),
        })
        for d, c in faxes:
            for page, snip in c["ev"].items():
                out["_details"].append({
                    "Fax Number": pretty(d), "Fax score": c["fax"], "Phone score": c["phone"],
                    "Pages with this fax": len(c["pages"]), "Page URL": page, "Evidence": snip})
    elif ok_pages == 0:
        out.update({"Status": "Website unreachable", "Evidence": "Could not load any page."})
    else:
        out.update({"Status": "No fax listed on website",
                    "Evidence": f"No number labeled Fax in {ok_pages} loaded page(s)."})
    return out


# --------------------------------------------------------------------- main
def pick_url_column(df):
    for c in df.columns:
        if re.search("website|url|link|site|web", str(c), re.I):
            return c
    def score(c):
        return sum(bool(re.search(r"\.[a-z]{2,}", str(v), re.I)) and " " not in str(v).strip()
                   for v in df[c])
    return max(df.columns, key=score)


COLUMNS = ["Fax Number", "Fax Confidence", "Status", "Fax Count", "Other Fax Numbers",
           "Phone Numbers (reference)", "Evidence", "Fax Found On",
           "Pages checked", "Pages loaded", "Crawl complete", "Error"]
RETRY = {"No fax listed on website", "Website unreachable"}


def run_site(website_raw, fetch, max_pages=None):
    website = clean_url(website_raw)
    if not website:
        return {"Status": "Invalid/missing URL", "_details": []}
    try:
        return process_site(website, fetch, max_pages)
    except Exception as exc:
        return {"Status": "Error", "Error": f"{type(exc).__name__}: {exc}", "_details": []}


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
            print(f"{n}/{len(unique)}: {u} -> {r.get('Fax Number') or r['Status']} "
                  f"({r.get('Fax Count', 0)} fax, {r.get('Pages checked', 0)} pages)")

    if USE_BROWSER_FALLBACK:
        todo = [u for u, r in results.items() if u and r.get("Status") in RETRY]
        if todo:
            print(f"\nBrowser pass for {len(todo)} sites...")
            browser = BrowserFetcher()
            try:
                for n, u in enumerate(todo, 1):
                    r = run_site(u, browser, BROWSER_MAX_PAGES)
                    if r.get("Status") == "Fax found":
                        results[u] = r
                    print(f"  {n}/{len(todo)}: {u} -> {r.get('Fax Number') or r['Status']}")
            finally:
                browser.close()

    res = pd.DataFrame([results[clean_url(v)] for v in df[url_col]]).reindex(columns=COLUMNS).fillna("")
    out = pd.concat([df.reset_index(drop=True), res], axis=1)

    detail_rows = [{"Website": u, **d} for u, r in results.items() for d in r.get("_details", [])]
    detail_cols = ["Website", "Fax Number", "Fax score", "Phone score",
                   "Pages with this fax", "Page URL", "Evidence"]
    with pd.ExcelWriter(OUTPUT_FILE) as xw:
        out.to_excel(xw, sheet_name="Results", index=False)
        pd.DataFrame(detail_rows, columns=detail_cols).to_excel(xw, sheet_name="All Fax Locations", index=False)
    print("\nSummary:\n", out["Status"].value_counts().to_string())
    print(f"\nFinished. Results saved to: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
