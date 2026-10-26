"""
COLLECTOR (Agent 6, part 1) - finds public business emails of Pakistani exporters.

It has 5 parts that share one to-do list (the "queue" tab of the Google Sheet):
  LISTER   reads directories, member lists and PDFs, and follows their "next page" links and site maps
  SEARCHER runs free web searches (sector x city, associations, fairs, business pages in search results)
  MAPPER   asks OpenStreetMap for companies in each industrial city (name, website, sometimes email)
  VISITOR  opens company websites (home + contact/about pages) and reads their public emails
  SCORER   remembers which websites gave emails; good sources go first, empty ones get skipped

Rules: public business emails only, max 3 per company, respects robots.txt, reads slowly.
Saves into the "emails" tab; writes a summary of every shift into the "runs" tab.
"""

import os, re, io, json, time, random, datetime
from urllib.parse import urljoin, urlparse, parse_qs, unquote
from urllib.robotparser import RobotFileParser

import requests
from bs4 import BeautifulSoup
from pypdf import PdfReader
import dns.resolver
import gspread
from google.oauth2.service_account import Credentials

# ---------------- settings ----------------
MAX_MINUTES = float(os.getenv("MAX_MINUTES", "22"))   # one shift; the trigger comes every 30 minutes
MAX_JOBS = int(os.getenv("MAX_JOBS", "80"))
MAX_SEARCHES = int(os.getenv("MAX_SEARCHES", "10"))   # web searches per shift (avoid being blocked)
MAX_GEMINI = int(os.getenv("MAX_GEMINI_CALLS", "15"))
MAX_DEPTH = 2                                          # how far it follows links inside a directory
PER_COMPANY = 3                                        # max emails from one company domain
GEMINI_KEY = os.getenv("GEMINI_API_KEY", "")
UA = "AgencyCollector/2.0 (academic survey research, Metropolitan University Karachi)"
BROWSER_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"

EMAIL_HEADERS = ["email", "company", "type", "sector", "city", "website", "source", "source_url",
                 "date_found", "email_check", "taken", "notes", "quality"]
QUEUE_HEADERS = ["kind", "value", "source", "added", "status", "note", "depth", "found"]
RUNS_HEADERS = ["time", "agent", "jobs_done", "new_emails", "duplicates", "bad_emails", "errors", "summary"]

FREE_MAIL = {"gmail.com", "yahoo.com", "hotmail.com", "outlook.com", "live.com", "ymail.com", "yahoo.co.uk",
             "aol.com", "icloud.com", "msn.com", "cyber.net.pk", "brain.net.pk", "hotmail.co.uk", "proton.me"}
JUNK = ("example.", "sentry", "wixpress", "domain.com", "yourname", "youremail", "email.com", "@2x", ".png",
        ".jpg", ".jpeg", ".gif", ".webp", ".svg", "noreply", "no-reply", "donotreply", "godaddy", "wordpress",
        "user@", "name@", "test@", "abuse@", "privacy@", "webmaster@", "postmaster@", "hostmaster@",
        ".gov.pk", "@gov.pk", "u003e", "%20")
SKIP_SITES = ("facebook.", "twitter.", "x.com", "instagram.", "linkedin.", "youtube.", "google.", "whatsapp.",
              "pinterest.", "tiktok.", "wikipedia.", "apple.com", "microsoft.", "amazon.", "duckduckgo.",
              "bing.com", "yahoo.com", "scribd.", "issuu.", "openstreetmap.")
DIRECTORY_SITES = ("alibaba.", "indiamart.", "tradeindia.", "exportersindia.", "made-in-china.", "kompass.",
                   "dnb.com", "zoominfo.", "opencorporates.", "bloomberg.", "crunchbase.", "brecorder.",
                   "dawn.com", "tribune.", "thenews.", "propakistani.", "app.com.pk")
LISTING_WORDS = ("member", "directory", "exporter", "exhibitor", "list", "company", "companies", "page",
                 "participant", "supplier", "manufacturer", "business", "category", "sector", "brochure", "pdf")
CONTACT_WORDS = ("contact", "about", "reach", "enquir", "inquir", "get-in-touch", "team", "office")
GOOD_PREFIX = ("export", "sales", "info", "contact", "marketing", "trade", "business", "ceo", "md", "director",
               "office", "admin", "mail")
FOREIGN_TLD = (".in", ".bd", ".lk", ".np", ".ir", ".af")
NOT_BUSINESS = ("hospital", "clinic", "medical cent", "school", "college", "university", "academy", "institute of",
                "apartment", "residen", "heights", "towers", "homes", "housing", "hotel", "restaurant", "cafe",
                "fitness", "gym", "salon", "beauty", "wedding", "banquet", "marquee", "church", "mosque", "masjid",
                "press club", "club", "hostel", "pharmacy", "dental", "eye cent", "eye hosp", "maternity", "plaza")


TRADE_BODY_RE = re.compile(r"(\bcci|cci\b|cci[0-9._]|chamber|association|assoc\b|council|federation|fpcci|tdap|"
                           r"\.gov|ministry|pasha\.|aptma|@reap\.|pcfa@|phma|prgmea|simap|psgmea|\.edu|university|"
                           r"wccis|wcci|gbcci|towelassociation)", re.I)
HIGH_SOURCES = ("tdap", "pcfa", "towel", "reap", "aptma", "prgmea", "phma", "psgmea", "simap", "plgmea", "pfva",
                "exhib", "exporter", "salt-exporters", "foodag", "brochure")
EXPORT_WORDS = ("export", "international buyers", "worldwide", "global clients", "overseas", "shipping worldwide",
                "fob", "incoterm", "our buyers in", "we supply to")


def quality_of(email, company, source, source_url, page_text=""):
    """high / medium / low / trade_body / remove - decides who the Sender emails first."""
    e = (email or "").lower()
    if "@" not in e:
        return "remove"
    local, d = e.split("@", 1)
    if d in FREE_MAIL and (len(local) < 4 or local.isdigit()):
        return "remove"
    if TRADE_BODY_RE.search(e) or TRADE_BODY_RE.search(company or ""):
        return "trade_body"
    src = f"{source} {source_url}".lower()
    if any(k in src for k in HIGH_SOURCES):
        return "high"
    if page_text and any(w in page_text.lower() for w in EXPORT_WORDS):
        return "high"
    if "fpcci" in src or "chamber" in src or "cci" in src or "company website" in src:
        return "medium"
    return "low"


def not_business(name):
    n = (name or "").lower()
    return any(w in n for w in NOT_BUSINESS)


EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,10}")

SECTORS = ["rice", "textile", "garments", "towel", "bedsheet", "denim", "knitwear", "hosiery", "leather",
           "footwear", "sports goods", "surgical instruments", "gloves", "cutlery", "seafood", "fruit",
           "vegetables", "mango", "kinnow", "dates", "onion potato", "meat", "poultry", "dairy", "honey", "spices",
           "dry fruits", "himalayan salt", "marble", "gemstones", "carpets", "handicrafts", "furniture",
           "pharmaceutical", "herbal products", "cosmetics", "chemicals", "plastics", "packaging", "paper", "glass",
           "ceramics", "cement", "sugar ethanol", "engineering goods", "auto parts", "software IT",
           "musical instruments"]
CITIES = ["Karachi", "Lahore", "Faisalabad", "Sialkot", "Gujranwala", "Wazirabad", "Multan", "Islamabad",
          "Rawalpindi", "Peshawar", "Quetta", "Hyderabad", "Kasur", "Chiniot"]
BODY_SEARCHES = [
    "TDAP exporters list pdf", "Pakistan Trade Portal exporters", "PSEB registered IT companies list",
    "SMEDA directory exporters", "Karachi Export Processing Zone units list",
    "FPCCI members list pdf email", "KCCI members directory", "LCCI members directory", "FCCI members list",
    "Sialkot Chamber of Commerce members list", "Gujranwala Chamber members list", "Multan Chamber members list",
    "Rawalpindi Chamber members list", "Islamabad Chamber members list", "Hyderabad Chamber members list",
    "Peshawar Chamber members list", "Quetta Chamber members list", "women chamber of commerce Pakistan members",
    "SITE Association of Industry Karachi members", "Korangi Association of Trade and Industry members",
    "North Karachi Association of Trade and Industry members", "FB Area Association of Trade and Industry members",
    "Landhi Association of Trade and Industry members", "Bin Qasim Association of Trade and Industry members",
    "REAP rice exporters association members", "APTMA members list", "PRGMEA members list",
    "PHMA hosiery members list", "PCFA members list", "Towel Manufacturers Association members",
    "Pakistan Textile Exporters Association members", "Pakistan Bedwear Exporters Association members",
    "Pakistan Tanners Association members", "PLGMEA leather garments members", "Pakistan Footwear Manufacturers members",
    "PSGMEA sports goods members Sialkot", "SIMAP surgical instruments members Sialkot",
    "Pakistan Gloves Manufacturers Exporters Association members", "PCSIMA cutlery Wazirabad members",
    "PFVA fruit vegetable exporters members", "Pakistan fisheries exporters association members",
    "Pakistan meat exporters association members", "P@SHA members list", "PPMA pharmaceutical members list",
    "Pakistan marble association members", "gems jewellery Pakistan exporters members",
    "Pakistan Carpet Manufacturers Exporters Association members", "Pakistan handicrafts exporters association",
    "Pakistan chemical manufacturers association members", "Pakistan plastic manufacturers association members",
    "PAAPAM auto parts members", "Himalayan salt exporters Pakistan list", "OICCI members list",
    "Pakistan Business Council members", "FPCCI business council members", "PIFFA freight forwarders members list",
    "Karachi Customs Agents Association members", "Expo Pakistan exhibitors list", "TEXPO exhibitors list",
    "Food Ag Pakistan exhibitors", "ITCN Asia exhibitors list", "IGATEX exhibitors list",
    "Pakistan Mega Leather Show exhibitors", "Expo Centre Karachi exhibitors list",
    "Gulfood Pakistan pavilion exhibitors", "Heimtextil Pakistan exhibitors", "Medica Pakistan exhibitors Sialkot",
    "ISPO Pakistan exhibitors", "Canton Fair Pakistan exhibitors", "Anuga Pakistan exhibitors",
    "FPCCI export trophy winners list", "Pakistan Halal Authority certified companies list",
    "Pakistan embassy commercial section Pakistani exporters list", "Jamal yellow pages Pakistan exporters",
    "Pakistan yellow pages exporters",
]
OSM_CITIES = ["Karachi", "Lahore", "Faisalabad", "Sialkot", "Gujranwala", "Multan", "Islamabad", "Rawalpindi",
              "Peshawar", "Hyderabad", "Quetta", "Kasur", "Wazirabad", "Chiniot"]

START = time.time()
stats = {"jobs": 0, "new": 0, "dups": 0, "bad": 0, "errors": 0, "searches": 0}
gemini_calls = 0
search_blocked = False


def pk_now():
    return (datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(hours=5)).strftime("%Y-%m-%d %H:%M")


def log(msg):
    print(f"[Collector {pk_now()}] {msg}", flush=True)


def time_left(margin=0.0):
    return (time.time() - START) / 60 < MAX_MINUTES - margin


def domain_of(url):
    try:
        u = url if url.startswith("http") else "https://" + url
        return urlparse(u).netloc.lower().split(":")[0].replace("www.", "")
    except Exception:
        return ""


def mask(e):
    return f"{e[:2]}***@{e.split('@')[1]}"


# ---------------- Google Sheet ----------------
def open_sheet():
    info = json.loads(os.environ["GOOGLE_CREDENTIALS"])
    creds = Credentials.from_service_account_info(info, scopes=["https://www.googleapis.com/auth/spreadsheets"])
    return gspread.authorize(creds).open_by_key(os.environ["SHEET_ID"].strip())


def get_tab(sh, name, headers):
    try:
        ws = sh.worksheet(name)
        if not ws.row_values(1):
            ws.update([headers], "A1")
        return ws
    except gspread.WorksheetNotFound:
        ws = sh.add_worksheet(title=name, rows=5000, cols=len(headers))
        ws.update([headers], "A1")
        log(f"Created tab '{name}'")
        return ws


# ---------------- web ----------------
_robots = {}
session = requests.Session()


def allowed(url):
    p = urlparse(url)
    base = f"{p.scheme}://{p.netloc}"
    if base not in _robots:
        rp = RobotFileParser()
        try:
            r = session.get(base + "/robots.txt", headers={"User-Agent": UA}, timeout=10)
            rp.parse(r.text.splitlines() if r.status_code == 200 else [])
        except Exception:
            rp.parse([])
        _robots[base] = rp
    return _robots[base].can_fetch(UA, url)


def fetch(url, timeout=25):
    """Returns {'text','links','title','url','xml'} or None. Reads HTML pages, PDFs and XML site maps."""
    if not url.startswith("http"):
        url = "https://" + url
    if not allowed(url):
        log(f"  robots.txt says no: {url[:80]}")
        return None
    time.sleep(1.2)
    r = session.get(url, headers={"User-Agent": UA}, timeout=timeout)
    r.raise_for_status()
    ctype = r.headers.get("content-type", "").lower()
    final = r.url
    if "pdf" in ctype or final.lower().endswith(".pdf"):
        reader = PdfReader(io.BytesIO(r.content))
        text = "\n".join((pg.extract_text() or "") for pg in reader.pages[:400])
        return {"text": text, "links": [], "title": "", "url": final, "xml": False}
    if "xml" in ctype or final.lower().endswith(".xml"):
        locs = re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", r.text)
        return {"text": "", "links": locs, "title": "", "url": final, "xml": True}
    soup = BeautifulSoup(r.text, "html.parser")
    links = []
    for a in soup.find_all("a", href=True):
        h = a["href"].strip()
        links.append(h if h.lower().startswith("mailto:") else urljoin(final, h))
    title = ""
    og = soup.find("meta", property="og:site_name")
    if og and og.get("content"):
        title = og["content"].strip()
    elif soup.title and soup.title.string:
        title = soup.title.string.strip()
    for t in soup(["script", "style", "noscript"]):
        t.decompose()
    return {"text": soup.get_text(" ", strip=True), "links": links, "title": title, "url": final, "xml": False}


def web_search(query, max_results=10):
    """Free DuckDuckGo search. Returns (links, snippet_text)."""
    global search_blocked
    if search_blocked or stats["searches"] >= MAX_SEARCHES:
        return None, ""
    stats["searches"] += 1
    for url in ("https://html.duckduckgo.com/html/", "https://lite.duckduckgo.com/lite/"):
        try:
            time.sleep(random.uniform(3, 6))
            r = session.post(url, data={"q": query, "kl": "pk-en"}, timeout=20, headers={"User-Agent": BROWSER_UA})
            if r.status_code != 200:
                continue
            soup = BeautifulSoup(r.text, "html.parser")
            links = []
            for a in soup.find_all("a", href=True):
                h = a["href"]
                if "uddg=" in h:
                    h = unquote(parse_qs(urlparse(h).query).get("uddg", [""])[0])
                if h.startswith("http") and "duckduckgo.com" not in h and h not in links:
                    links.append(h)
            if links:
                return links[:max_results], soup.get_text(" ", strip=True)
        except Exception as ex:
            log(f"  web search problem: {type(ex).__name__}")
    search_blocked = True
    log("  Web search is not answering (maybe blocked for now). Searches paused for this shift.")
    return None, ""


# ---------------- emails ----------------
def find_emails(text, links=()):
    t = re.sub(r"\s*[\[\(\{]\s*at\s*[\]\)\}]\s*", "@", text, flags=re.I)
    t = re.sub(r"\s*[\[\(\{]\s*dot\s*[\]\)\}]\s*", ".", t, flags=re.I)
    found = set(EMAIL_RE.findall(t))
    for l in links:
        if l.lower().startswith("mailto:"):
            found.update(EMAIL_RE.findall(unquote(l)))
    out = set()
    for e in found:
        c = clean_email(e)
        if c:
            out.add(c)
    return out


def clean_email(e):
    e = (e or "").strip().strip(".,;:'\"()<>").lower()
    if not EMAIL_RE.fullmatch(e) or any(j in e for j in JUNK) or len(e) > 80:
        return None
    local, d = e.split("@", 1)
    if d in FREE_MAIL and (len(local) < 4 or local.isdigit()):
        return None   # broken piece of an email split across two lines in a PDF
    return e


_mx = {}


def check_email(email):
    domain = email.split("@")[1]
    if domain in FREE_MAIL:
        return "ok_freemail"
    if domain not in _mx:
        try:
            dns.resolver.resolve(domain, "MX", lifetime=8)
            _mx[domain] = "ok"
        except Exception:
            _mx[domain] = "no_mx"
    return _mx[domain]


def rank_email(e):
    local = e.split("@")[0]
    return (0 if local.startswith(GOOD_PREFIX) else 1, len(local))


# ---------------- Gemini (only for reading company names; never needed for emails) ----------------
MODELS = [m for m in [os.getenv("GEMINI_MODEL", "")] if m] + ["gemini-3.5-flash-lite", "gemini-flash-latest"]


def pick_models():
    global MODELS
    if not GEMINI_KEY:
        return "no Gemini key"
    try:
        r = session.get("https://generativelanguage.googleapis.com/v1beta/models",
                        headers={"x-goog-api-key": GEMINI_KEY}, params={"pageSize": 200}, timeout=30)
        names = []
        for m in r.json().get("models", []):
            n = m.get("name", "").replace("models/", "")
            if "generateContent" in m.get("supportedGenerationMethods", []) and "flash" in n and not any(
                    x in n for x in ("image", "tts", "audio", "live", "thinking", "embedding", "exp")):
                names.append(n)

        def score(n):
            v = re.findall(r"(\d+(?:\.\d+)?)", n)
            return ("preview" in n, "latest" in n, "lite" not in n, -(float(v[0]) if v else 0))
        names.sort(key=score)
        if names:
            MODELS = names[:4]
        return "models: " + ", ".join(MODELS[:2])
    except Exception as ex:
        return f"model list problem ({type(ex).__name__})"


def gemini(prompt):
    global gemini_calls
    if not GEMINI_KEY or gemini_calls >= MAX_GEMINI:
        return None
    body = {"contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": {"responseMimeType": "application/json", "temperature": 0}}
    for m in list(MODELS):
        try:
            r = session.post(f"https://generativelanguage.googleapis.com/v1beta/models/{m}:generateContent",
                             headers={"x-goog-api-key": GEMINI_KEY}, json=body, timeout=60)
        except Exception:
            continue
        gemini_calls += 1
        if r.status_code in (404, 429, 500, 503):
            if r.status_code in (404, 429) and m in MODELS:
                MODELS.remove(m)
            continue
        if r.status_code != 200:
            return None
        time.sleep(5)
        try:
            t = "".join(p.get("text", "") for p in r.json()["candidates"][0]["content"]["parts"])
            t = t.strip().replace("```json", "").replace("```", "")
            a, b = (t.find("["), t.rfind("]")) if "[" in t else (t.find("{"), t.rfind("}"))
            return json.loads(t[a:b + 1])
        except Exception:
            return None
    gemini_calls = MAX_GEMINI
    return None


EXTRACT_PROMPT = """This is part of a Pakistani business directory, member list or exporter list.
List each company in it as a JSON array of objects:
{"company":"", "email":"", "website":"", "city":"", "sector":""}
Copy emails and websites exactly as written; leave a field empty if it is not in the text. Do not invent anything.

TEXT:
"""


# ---------------- the agent ----------------
class Collector:
    def __init__(self):
        sh = open_sheet()
        self.ws_emails = get_tab(sh, "emails", EMAIL_HEADERS)
        self.ws_queue = get_tab(sh, "queue", QUEUE_HEADERS)
        self.ws_runs = get_tab(sh, "runs", RUNS_HEADERS)
        self.cleanup()
        rows = self.ws_emails.get_all_values()[1:]
        self.known = {r[0].strip().lower() for r in rows if r and r[0]}
        self.per_domain = {}
        for e in self.known:
            d = e.split("@")[1] if "@" in e else ""
            self.per_domain[d] = self.per_domain.get(d, 0) + 1
        self.queue = self.ws_queue.get_all_values()
        self.qvalues = {r[1].strip().lower() for r in self.queue[1:] if len(r) > 1}
        self.new_rows, self.new_jobs, self.updates = [], [], []
        self.last_flush = time.time()
        # SCORER: how useful each website has been so far
        self.dom_jobs, self.dom_found = {}, {}
        for r in self.queue[1:]:
            r = r + [""] * (8 - len(r))
            if r[4] == "done" and r[0] in ("url", "site"):
                d = domain_of(r[1])
                self.dom_jobs[d] = self.dom_jobs.get(d, 0) + 1
                self.dom_found[d] = self.dom_found.get(d, 0) + (int(r[7]) if r[7].isdigit() else 0)
        log(f"Start: {len(self.known)} emails in the sheet, {len(self.queue) - 1} jobs in the queue")

    def cleanup(self):
        """Removes rows from the old map search (wrong Hyderabad, hospitals, schools...) and foreign domains."""
        try:
            if self.ws_emails.col_count < 13:
                self.ws_emails.add_cols(13 - self.ws_emails.col_count)   # room for the quality column
        except Exception:
            pass
        allrows = self.ws_emails.get_all_values()
        if len(allrows) < 2:
            return
        keep = [allrows[0]]
        removed = old_maps = 0
        for r in allrows[1:]:
            r = r + [""] * (13 - len(r))
            d = r[0].split("@")[1] if "@" in r[0] else ""
            old_map = r[6] == "OpenStreetMap" and r[11] != "osm-v2"
            if old_map or d.endswith(FOREIGN_TLD) or not_business(r[1]):
                removed += 1
                old_maps += old_map
            else:
                keep.append(r)
        # give every row a quality label (old rows were saved before labels existed)
        if not removed:
            header = keep[0] + [""] * (13 - len(keep[0]))
            missing = [i for i, r in enumerate(keep[1:], start=2) if not r[12:13] or not r[12]]
            if header[12] != "quality" or missing:
                labels = [["quality"]] + [[r[12] if len(r) > 12 and r[12] else
                                           quality_of(r[0], r[1], r[6], r[7])] for r in keep[1:]]
                self.ws_emails.update(labels, f"M1:M{len(labels)}", value_input_option="RAW")
                log(f"Quality labels added to {len(missing)} rows")
            return
        if removed:
            for r in keep[1:]:
                if len(r) < 13 or not r[12]:
                    r[12:13] = [quality_of(r[0], r[1], r[6], r[7])]
            keep[0] = (keep[0] + [""] * 13)[:12] + ["quality"]
            self.ws_emails.clear()
            self.ws_emails.update(keep, "A1", value_input_option="RAW")
            log(f"Cleanup: removed {removed} rows that were not Pakistani businesses")
            if not old_maps:
                return
            q = self.ws_queue.get_all_values()
            ups = [{"range": f"E{i + 1}:H{i + 1}", "values": [["pending", "redo with Pakistan-only map", "0", ""]]}
                   for i, r in enumerate(q) if i > 0 and r and r[0] == "osm" and (len(r) < 5 or r[4] != "pending")]
            if ups:
                self.ws_queue.batch_update(ups)

    # ----- queue -----
    def add_job(self, kind, value, source, depth=0):
        v = (value or "").strip()
        if not v or v.lower() in self.qvalues or len(v) > 400:
            return False
        if kind in ("url", "site"):
            d = domain_of(v)
            if not d or any(s in d for s in SKIP_SITES):
                return False
            if kind == "site" and (any(s in d for s in DIRECTORY_SITES) or self.per_domain.get(d, 0) >= PER_COMPANY):
                return False
        self.qvalues.add(v.lower())
        self.new_jobs.append([kind, v, source[:120], pk_now(), "pending", "", str(depth), ""])
        return True

    def add_seeds(self):
        if os.path.exists("sources.txt"):
            for line in open("sources.txt", encoding="utf-8"):
                line = line.split(" #")[0].strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("sitemap:"):
                    self.add_job("sitemap", line[8:].strip(), "sources.txt")
                else:
                    self.add_job("url", line, "sources.txt")
        for c in OSM_CITIES:
            self.add_job("osm", c, "maps")
        for q in BODY_SEARCHES:
            self.add_job("search", q, "plan: trade bodies, fairs, lists")
        for sec in SECTORS:
            for city in CITIES:
                self.add_job("search", f"{sec} exporter {city} email", "plan: sector x city")
        for sec in SECTORS:
            self.add_job("search", f'"{sec}" exporter Pakistan "@gmail.com" OR "@yahoo.com" contact',
                         "plan: business pages in search results")

    # ----- saving -----
    def save(self, email, company="", typ="exporter", sector="", city="", website="", source="", source_url="",
             note="", page_text=""):
        email = clean_email(email)
        if not email:
            return False
        if email in self.known:
            stats["dups"] += 1
            return False
        d = email.split("@")[1]
        if d.endswith(FOREIGN_TLD) or not_business(company):
            return False
        if d not in FREE_MAIL and self.per_domain.get(d, 0) >= PER_COMPANY:
            return False
        chk = check_email(email)
        if chk == "no_mx":
            stats["bad"] += 1
            return False
        if not company and chk == "ok":
            company = d.split(".")[0].title()
        self.known.add(email)
        self.per_domain[d] = self.per_domain.get(d, 0) + 1
        self.new_rows.append([email, (company or "")[:80], typ, (sector or "")[:40], (city or "")[:40],
                              website, source[:80], source_url[:300], pk_now(), chk, "", note,
                              quality_of(email, company, source, source_url, page_text)])
        stats["new"] += 1
        log(f"  + {mask(email)}  ({company or 'unknown company'})")
        return True

    # ----- LISTER -----
    def do_url(self, url, source, depth):
        page = fetch(url)
        if not page:
            return 0, "skipped (robots)"
        if page["xml"]:
            return 0, self._queue_links(page["links"], url, depth, from_sitemap=True)
        new = 0
        here = domain_of(page["url"])
        for e in sorted(find_emails(page["text"], page["links"]), key=rank_email):
            new += self.save(e, source=source or here, source_url=page["url"], note="from list")
        # Gemini adds company names for list pages that show names + websites but no emails
        entries = []
        if new < 5 and page["text"] and gemini_calls < MAX_GEMINI:
            res = gemini(EXTRACT_PROMPT + page["text"][:9000])
            entries = [x for x in res if isinstance(x, dict)] if isinstance(res, list) else []
            for x in entries:
                if x.get("email"):
                    new += self.save(x["email"], x.get("company", ""), "exporter", x.get("sector", ""),
                                     x.get("city", ""), x.get("website", ""), source or here, page["url"])
                elif x.get("website"):
                    self.add_job("site", x["website"], page["url"], depth + 1)
                elif x.get("company"):
                    self.add_job("company", f'{x["company"]} {x.get("city", "")}'.strip(), page["url"])
        note = self._queue_links(page["links"], page["url"], depth) if depth < MAX_DEPTH else ""
        return new, f"{new} new{', ' + note if note else ''}"

    def _queue_links(self, links, base, depth, from_sitemap=False):
        here = domain_of(base)
        added_pages = added_sites = 0
        for l in links[:600]:
            if not l.startswith("http"):
                continue
            d = domain_of(l)
            low = l.lower()
            if d == here:
                useful = low.endswith(".pdf") or low.endswith(".xml") or any(w in low for w in LISTING_WORDS)
                if useful and added_pages < 40:
                    added_pages += self.add_job("url", l.split("#")[0], f"inside {here}", depth + 1)
            elif not from_sitemap and d and added_sites < 40:
                added_sites += self.add_job("site", f"https://{d}", base, depth + 1)
        return f"{added_pages} pages + {added_sites} company sites queued"

    def do_sitemap(self, site, source):
        base = site if site.startswith("http") else "https://" + site
        base = f"{urlparse(base).scheme}://{urlparse(base).netloc}"
        total = 0
        for path in ("/wp-sitemap.xml", "/sitemap_index.xml", "/sitemap.xml"):
            try:
                p = fetch(base + path, timeout=20)
            except Exception:
                continue
            if p and p["links"]:
                for l in p["links"][:800]:
                    low = l.lower()
                    if low.endswith(".xml"):
                        total += self.add_job("sitemap-part", l, f"sitemap of {domain_of(base)}")
                    elif low.endswith(".pdf") or any(w in low for w in LISTING_WORDS):
                        total += self.add_job("url", l, f"sitemap of {domain_of(base)}", 1)
                break
        return 0, f"{total} pages found in site map"

    def do_sitemap_part(self, url, source):
        p = fetch(url, timeout=20)
        n = 0
        for l in (p["links"] if p else [])[:1500]:
            low = l.lower()
            if low.endswith(".pdf") or any(w in low for w in LISTING_WORDS):
                n += self.add_job("url", l, source, 1)
        return 0, f"{n} pages queued"

    # ----- VISITOR -----
    def do_site(self, site, source, depth):
        page = fetch(site)
        if not page:
            return 0, "skipped (robots)"
        here = domain_of(page["url"])
        pages = [page]
        extra = [l for l in page["links"] if domain_of(l) == here and any(w in l.lower() for w in CONTACT_WORDS)]
        for l in list(dict.fromkeys(extra))[:2]:
            try:
                p = fetch(l)
                if p:
                    pages.append(p)
            except Exception:
                pass
        emails = set()
        for p in pages:
            emails |= find_emails(p["text"], p["links"])
        own = [e for e in emails if e.split("@")[1].endswith(here) or e.split("@")[1] in FREE_MAIL]
        company = re.split(r"\s[|\-–]\s", page["title"])[0][:80] if page["title"] else ""
        new = 0
        for e in sorted(own or emails, key=rank_email)[:PER_COMPANY]:
            new += self.save(e, company, "exporter", website=f"https://{here}", source="company website",
                             source_url=page["url"], page_text=" ".join(p["text"][:20000] for p in pages))
        return new, f"{new} new" if emails else "no email on site"

    # ----- SEARCHER -----
    def do_search(self, query, source):
        links, text = web_search(query)
        if links is None:
            raise RuntimeError("WAIT")
        new = 0
        for e in find_emails(text):  # emails shown right in the search results (incl. business pages)
            new += self.save(e, source="search results", source_url=f"search: {query[:60]}", note=query[:60])
        lists = sites = 0
        for l in links:
            d = domain_of(l)
            low = l.lower()
            if any(s in d for s in SKIP_SITES):
                continue
            if low.endswith(".pdf") or any(w in low for w in LISTING_WORDS) or "plan: trade" in source:
                lists += self.add_job("url", l, f"search: {query[:60]}", 0)
            elif not any(s in d for s in DIRECTORY_SITES):
                sites += self.add_job("site", f"https://{d}", f"search: {query[:60]}", 1)
        return new, f"{new} new from results, {lists} lists + {sites} sites queued"

    def do_company(self, name, source):
        links, _ = web_search(f"{name} Pakistan official website contact")
        if links is None:
            raise RuntimeError("WAIT")
        for l in links:
            d = domain_of(l)
            if d and not any(s in d for s in SKIP_SITES + DIRECTORY_SITES) and not l.lower().endswith(".pdf"):
                n, note = self.do_site(f"https://{d}", source, 1)
                return n, "site: " + note
        return 0, "website not found"

    # ----- MAPPER (OpenStreetMap) -----
    def do_osm(self, city, source):
        q = f"""[out:json][timeout:120];
area["ISO3166-1"="PK"][admin_level=2]->.pk;
area[~"^name(:en)?$"~"^{city}$"]["boundary"="administrative"]->.a;
(
  nwr(area.a)(area.pk)["office"~"company|industrial|association|logistics|export|import|it"][~"^(contact:)?(email|website)$"~"."];
  nwr(area.a)(area.pk)["industrial"][~"^(contact:)?(email|website)$"~"."];
  nwr(area.a)(area.pk)["man_made"="works"][~"^(contact:)?(email|website)$"~"."];
  nwr(area.a)(area.pk)["craft"][~"^(contact:)?(email|website)$"~"."];
  nwr(area.a)(area.pk)["shop"="wholesale"][~"^(contact:)?(email|website)$"~"."];
  nwr(area.a)(area.pk)["landuse"="industrial"]["name"][~"^(contact:)?(email|website)$"~"."];
);
out tags;"""
        r = None
        for ep in ("https://overpass-api.de/api/interpreter", "https://overpass.kumi.systems/api/interpreter"):
            try:
                r = session.post(ep, data={"data": q}, timeout=120, headers={"User-Agent": UA})
                if r.status_code == 200:
                    break
            except Exception:
                r = None
        if not r or r.status_code != 200:
            raise RuntimeError("WAIT")
        new = sites = 0
        for el in r.json().get("elements", []):
            t = el.get("tags", {})
            name = t.get("name:en") or t.get("name", "")
            if not_business(name):
                continue
            web = t.get("website") or t.get("contact:website") or ""
            for key in ("email", "contact:email"):
                for e in re.split(r"[;,\s]+", t.get(key, "")):
                    if e:
                        new += self.save(e, name, "company", t.get("industrial", t.get("office", "")), city, web,
                                         "OpenStreetMap", f"osm:{el.get('type')}/{el.get('id')}", note="osm-v2")
            if web:
                sites += self.add_job("site", web, f"OpenStreetMap {city}", 1)
        return new, f"{new} new, {sites} company sites queued"

    # ----- one shift -----
    def run(self):
        info = pick_models()
        self.add_seeds()
        self.flush()
        self.queue = self.ws_queue.get_all_values()
        pending = []
        for i, r in enumerate(self.queue):
            if i == 0:
                continue
            r = r + [""] * (8 - len(r))
            if r[4] in ("", "pending"):
                pending.append((i + 1, r))
        # SCORER: skip websites that gave nothing 4+ times; prefer links found on productive websites
        def priority(item):
            row_no, r = item
            order = {"url": 0, "sitemap": 0, "sitemap-part": 1, "site": 2, "osm": 3, "search": 4, "company": 5}
            parent = domain_of(r[2].replace("inside ", "").replace("sitemap of ", ""))
            bonus = -min(self.dom_found.get(parent, 0), 50)
            return (order.get(r[0], 9), bonus, int(r[6]) if r[6].isdigit() else 0)
        pending.sort(key=priority)
        # mix kinds so one shift does a bit of everything
        pattern = ("url", "sitemap", "sitemap-part", "site", "site", "url", "osm", "search", "company")
        by_kind = {}
        for p in pending:
            if p[1][0] in pattern:
                by_kind.setdefault(p[1][0], []).append(p)
        plan, searches = [], 0
        while len(plan) < MAX_JOBS and any(by_kind.values()):
            for k in pattern:
                if not by_kind.get(k) or len(plan) >= MAX_JOBS:
                    continue
                if k in ("search", "company"):
                    if searches >= MAX_SEARCHES:
                        by_kind[k] = []
                        continue
                    searches += 1
                plan.append(by_kind[k].pop(0))
        log(f"Gemini {info} | {len(pending)} jobs waiting, planning {len(plan)} this shift")

        for row_no, r in plan:
            if not time_left(margin=1.5):
                log("Shift time is over.")
                break
            kind, value, source = r[0], r[1], r[2]
            d = domain_of(value)
            if kind in ("url", "site") and self.dom_jobs.get(d, 0) >= 4 and self.dom_found.get(d, 0) == 0:
                self.updates.append({"range": f"E{row_no}:H{row_no}", "values": [["skipped", "website gave nothing before", r[6], "0"]]})
                continue
            if kind in ("search", "company") and (search_blocked or stats["searches"] >= MAX_SEARCHES):
                continue
            log(f"Job [{kind}] {value[:90]}")
            try:
                depth = int(r[6]) if r[6].isdigit() else 0
                if kind == "url":
                    found, note = self.do_url(value, "", depth)
                elif kind == "site":
                    found, note = self.do_site(value, source, depth)
                elif kind == "sitemap":
                    found, note = self.do_sitemap(value, source)
                elif kind == "sitemap-part":
                    found, note = self.do_sitemap_part(value, source)
                elif kind == "osm":
                    found, note = self.do_osm(value, source)
                elif kind == "search":
                    found, note = self.do_search(value, source)
                else:
                    found, note = self.do_company(value, source)
                status = "done"
                self.dom_jobs[d] = self.dom_jobs.get(d, 0) + 1
                self.dom_found[d] = self.dom_found.get(d, 0) + found
            except RuntimeError as ex:
                if str(ex) == "WAIT":
                    continue
                status, note, found = "error", str(ex)[:100], 0
                stats["errors"] += 1
            except Exception as ex:
                status, note, found = "error", f"{type(ex).__name__}: {str(ex)[:90]}", 0
                stats["errors"] += 1
                log(f"  error: {note}")
            stats["jobs"] += 1
            self.updates.append({"range": f"E{row_no}:H{row_no}", "values": [[status, note[:150], r[6], str(found)]]})
            if len(self.updates) >= 10 or (self.new_rows and time.time() - self.last_flush > 15):
                self.flush()
        self.flush()
        left = sum(1 for _ in pending) - stats["jobs"]
        summary = (f"{stats['new']} new emails | total {len(self.known)} | {stats['jobs']} jobs done, ~{max(left, 0)} waiting | "
                   f"{stats['searches']} searches{' (search paused)' if search_blocked else ''} | "
                   f"{gemini_calls} Gemini calls")
        self.ws_runs.append_row([pk_now(), "Collector", stats["jobs"], stats["new"], stats["dups"], stats["bad"],
                                 stats["errors"], summary])
        log("Finished. " + summary)

    def flush(self):
        self.last_flush = time.time()
        if self.new_rows:
            self.ws_emails.append_rows(self.new_rows, value_input_option="RAW")
            self.new_rows = []
        if self.new_jobs:
            for i in range(0, len(self.new_jobs), 500):
                self.ws_queue.append_rows(self.new_jobs[i:i + 500], value_input_option="RAW")
            self.new_jobs = []
        if self.updates:
            self.ws_queue.batch_update(self.updates)
            self.updates = []


if __name__ == "__main__":
    Collector().run()
