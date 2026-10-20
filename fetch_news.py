#!/usr/bin/env python3
"""Playora news aggregator - standard library only.

Reads feeds.json, downloads every feed in parallel, normalises RSS/Atom items,
classifies them (playstation / xbox / nintendo / pc / mobile / esports / general),
removes duplicates and writes:

    <out>/news-en.json   <out>/news-ar.json   <out>/status.json   <out>/index.html

Only the headline, a short snippet, the thumbnail URL and a link back to the
original article are stored - readers are always sent to the publisher.

Usage:  python3 fetch_news.py --out site [--feeds feeds.json]
Exit code 1 when too few items were collected (so a CI run keeps the previous
deployment instead of publishing an empty feed).
"""
import argparse
import concurrent.futures as cf
import gzip
import hashlib
import html
import json
import pathlib
import re
import sys
import time
import urllib.parse
import urllib.request
import zlib
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from xml.etree import ElementTree as ET

UA = ("Mozilla/5.0 (compatible; PlayoraNewsBot/1.0; +https://example.com/bot) "
      "feed-reader")
MAX_BYTES = 6 * 1024 * 1024
ORDER = ["playstation", "xbox", "nintendo", "mobile", "pc", "esports"]

RULES = {
    "playstation": r"\b(playstation|ps5|ps4|ps\s?plus|psvr2?|dualsense|sony interactive|state of play)\b|بلايستيشن|بلاي ستيشن|سوني",
    "xbox": r"\b(xbox|game pass|gamepass|series [xs]|microsoft gaming)\b|إكس بوكس|اكس بوكس|إكسبوكس|قيم باس",
    "nintendo": r"\b(nintendo|switch 2|switch|zelda|mario|pok[eé]mon|splatoon|kirby|smash bros)\b|نينتندو|سويتش|بوكيمون",
    "mobile": r"\b(mobile|ios|android|iphone|ipad|app store|google play|gacha|genshin|pubg mobile|free fire|roblox|clash royale|clash of clans)\b|موبايل|جوال|هاتف|اندرويد|أندرويد|ايفون|آيفون|بابجي|روبلوكس",
    "pc": r"\b(pc|steam|steam deck|epic games|nvidia|geforce|rtx|amd|radeon|ryzen|gog|battle\.net)\b|ستيم|كمبيوتر|حاسوب|إنفيديا|انفيديا|بي سي",
    "esports": r"\b(esports?|tournament|championship|world cup|ewc|league of legends|valorant|dota 2|counter-strike|cs2)\b|إي سبورت|اي سبورت|بطولة|الرياضات الإلكترونية",
}
RULES = {k: re.compile(v, re.I) for k, v in RULES.items()}


# ----------------------------------------------------------------- helpers
def local(tag):
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def clean_text(s, limit=None):
    if not s:
        return ""
    s = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", s, flags=re.S | re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    s = html.unescape(s)
    s = re.sub(r"\s+", " ", s).strip()
    if limit and len(s) > limit:
        s = s[:limit].rsplit(" ", 1)[0].rstrip(" ,.;:-—") + "…"
    return s


def parse_date(raw):
    if not raw:
        return None
    raw = raw.strip()
    try:
        d = parsedate_to_datetime(raw)
    except Exception:
        d = None
    if d is None:
        try:
            d = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        except Exception:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=timezone.utc)
    return d.astimezone(timezone.utc)


def https(url):
    if not url:
        return ""
    url = url.strip()
    if url.startswith("//"):
        url = "https:" + url
    if url.startswith("http://"):
        url = "https://" + url[7:]
    return url if url.startswith("https://") else ""


def norm_url(url):
    p = urllib.parse.urlsplit(url)
    q = [(k, v) for k, v in urllib.parse.parse_qsl(p.query)
         if not k.lower().startswith(("utm_", "fbclid", "gclid", "ref"))]
    return urllib.parse.urlunsplit((p.scheme, p.netloc.lower(), p.path.rstrip("/"),
                                    urllib.parse.urlencode(q), ""))


def norm_title(t):
    return re.sub(r"[\W_]+", "", t.lower())


def http_get(url, timeout=20):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*",
        "Accept-Encoding": "gzip",
    })
    with urllib.request.urlopen(req, timeout=timeout) as r:
        data = r.read(MAX_BYTES + 1)
        if len(data) > MAX_BYTES:
            raise ValueError("feed too large")
        if r.headers.get("Content-Encoding") == "gzip" or data[:2] == b"\x1f\x8b":
            data = gzip.decompress(data)
        return data


def gnews_url(query, lang):
    q = urllib.parse.quote_plus(query + " when:2d")
    if lang == "ar":
        return f"https://news.google.com/rss/search?q={q}&hl=ar&gl=SA&ceid=SA:ar"
    return f"https://news.google.com/rss/search?q={q}&hl=en-US&gl=US&ceid=US:en"


# ------------------------------------------------------------------ parsing
IMG_RE = re.compile(r"<img[^>]+src=[\"']([^\"']+)[\"']", re.I)


SMALL_RE = re.compile(r"(-|_)(\d{2,3})x(\d{2,3})\.(jpe?g|png|webp)|[?&](w|width)=(\d{2,3})(&|$)|/(thumb|thumbs|thumbnail|small|tiny|icon)s?/|_(s|t|small|thumb)\.(jpe?g|png|webp)", re.I)


def looks_small(u):
    return bool(u) and bool(SMALL_RE.search(u))


def upgrade_image(u):
    """Turn well-known thumbnail URL patterns into the full-size picture the publisher serves."""
    if not u:
        return u
    u = re.sub(r"-\d{2,4}x\d{2,4}(\.(?:jpe?g|png|webp))", r"\1", u, flags=re.I)         # WordPress -300x200.jpg
    u = re.sub(r"([?&])(w|width)=\d+", r"\1\2=1280", u, flags=re.I)
    u = re.sub(r"([?&])(h|height)=\d+&?", r"\1", u, flags=re.I).rstrip("?&")
    return u


def media_width(c):
    try:
        return int(c.get("width") or 0)
    except ValueError:
        return 0


def parse_feed(data):
    root = ET.fromstring(data)
    out = []
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        it = {"title": "", "link": "", "date": None, "summary": "", "image": "", "source": ""}
        html_blobs = []
        for c in el:
            t = local(c.tag)
            txt = (c.text or "").strip()
            if t == "title":
                it["title"] = clean_text(txt)
            elif t == "link":
                if c.get("href"):
                    if c.get("rel") in (None, "alternate"):
                        it["link"] = c.get("href")
                elif txt:
                    it["link"] = txt
            elif t in ("pubDate", "published", "updated", "date") and not it["date"]:
                it["date"] = parse_date(txt)
            elif t in ("description", "summary"):
                it["summary"] = txt
                html_blobs.append(txt)
            elif t in ("encoded", "content"):
                html_blobs.append(txt)
            elif t == "source":
                it["source"] = clean_text(txt)
            if t in ("thumbnail", "content", "enclosure"):
                u = c.get("url") or c.get("href")
                typ = (c.get("type") or c.get("medium") or "").lower()
                if u and (t == "thumbnail" or "image" in typ or re.search(r"\.(jpe?g|png|webp)(\?|$)", u, re.I)):
                    w = media_width(c)
                    if not it["image"] or w > it.get("_w", 0):      # keep the widest variant the feed offers
                        it["image"], it["_w"] = u, w
            if t == "group":                       # <media:group>
                for g in c:
                    if local(g.tag) in ("thumbnail", "content") and g.get("url"):
                        w = media_width(g)
                        if not it["image"] or w > it.get("_w", 0):
                            it["image"], it["_w"] = g.get("url"), w
        if not it["image"]:
            for blob in html_blobs:
                m = IMG_RE.search(blob or "")
                if m:
                    it["image"] = m.group(1)
                    break
        it["image"] = upgrade_image(it["image"])
        it.pop("_w", None)
        it["summary"] = "" if it["summary"].lstrip().startswith("<a ") else clean_text(it["summary"], 200)
        if it["title"] and it["link"]:
            out.append(it)
    return out


def classify(text, hint):
    tags = [k for k in ORDER if RULES[k].search(text)]
    primary = hint or (tags[0] if tags else "general")
    if hint and hint not in tags:
        tags.insert(0, hint)
    return primary, tags[:3]


# ------------------------------------------------------------ topic filter
# Strict scope: video games, games companies, and computer-hardware companies ONLY.
CORE = re.compile(
    r"\b(video ?games?|gaming|gamers?|gameplay|esports?|dlc|game pass|playstation|ps[345]|psvr2?|xbox|nintendo|"
    r"switch 2|steam deck|steam|epic games|dualsense|joy-con|early access|patch notes)\b"
    r"|ألعاب الفيديو|الألعاب|ألعاب|لعبة|قيمنق|جيمنج|جيمر|قيمر|بلايستيشن|بلاي ستيشن|إكس ?بوكس|اكس ?بوكس|إكسبوكس|نينتندو|سويتش|ستيم|"
    r"الرياضات الإلكترونية|إي سبورت|اي سبورت", re.I)
COMPANY = re.compile(
    r"\b(valve|ubisoft|electronic arts|ea sports|ea games|activision|blizzard|bethesda|capcom|square enix|bandai namco|sega|konami|"
    r"rockstar|take-two|cd projekt|fromsoftware|riot games|hoyoverse|mihoyo|krafton|nexon|netease|tencent|supercell|roblox|minecraft|"
    r"mojang|bungie|embracer|devolver|2k games|remedy|paradox|gearbox|insomniac|naughty dog|santa monica|id software|playground games|"
    r"gta|call of duty|fortnite|valorant|league of legends|dota|counter-strike|cs2|apex legends|overwatch|diablo|zelda|mario|"
    r"pok[eé]mon|elden ring|witcher|cyberpunk|battlefield|ea fc|madden|genshin|honkai|pubg|free fire|clash of clans|clash royale|gacha)\b"
    r"|روكستار|يوبيسوفت|كابكوم|سيجا|كونامي|رايوت|بوكيمون|ماينكرافت|فورتنايت|ببجي|بابجي|روبلوكس", re.I)
HARDWARE = re.compile(
    r"\b(nvidia|geforce|rtx|amd|radeon|ryzen|intel|arc gpu|qualcomm|snapdragon x|graphics cards?|gpus?|cpus?|processors?|"
    r"motherboards?|ssds?|nvme|ddr[45]|pcie|ram kit|gaming (pc|pcs|laptops?|monitors?|mouse|mice|keyboards?|headsets?|chairs?|handheld)|"
    r"handheld pc|rog ally|legion go|steam deck|dell|lenovo|acer|asus|gigabyte|msi|razer|corsair|logitech|alienware|nzxt|"
    r"steelseries|hyperx|benq|viewsonic|samsung odyssey|lg ultragear|oled monitor|micron|western digital|kingston|crucial|"
    r"g\.skill|noctua|cooler master|thermaltake|lian li|framework laptop|ray tracing|dlss|fsr)\b"
    r"|إنفيديا|انفيديا|ايه ام دي|إيه إم دي|إنتل|انتل|كرت شاشة|كروت الشاشة|كرت الشاشة|بطاقة رسوميات|بطاقات رسومية|بطاقة رسومية|"
    r"معالج|معالجات|لابتوب|لابتوبات|كمبيوتر|حاسوب|ايسوس|أسوس|ريزر|كورسير|لينوفو|ديل", re.I)
DENY_HARD = re.compile(
    r"\b(betting|bookmakers?|casino|casinos|slots?|lottery|jackpot|poker|forex|gambling|sportsbook|odds)\b"
    r"|ألعاب القوى|الألعاب الأولمبية|الألعاب الآسيوية|الألعاب الخليجية|olympic games|مراهنات|كازينو|قمار|يانصيب|رهان|بيع عملات|شراء عملات|sell (game )?(gold|currency)|buy (game )?(gold|currency)", re.I)
DENY_SOFT = re.compile(
    r"\b(football|soccer|nba|nfl|nhl|mlb|ufc|premier league|champions league|la liga|serie a|world cup qualifier|olympics?|olympic games|"
    r"election|politic\w*|trump|biden|senate|parliament|gaza|ukraine|stocks?|shares|stock market|wall street|nasdaq|investors?|"
    r"price target|dividend|movie|film|tv series|season finale|box office|celebrity|recipe|weather|earthquake|crypto|bitcoin)\b"
    r"|كرة القدم|كرة|مباراة|مباريات|الدوري|كأس العالم لكرة|ملعب|الأولمبية|ألعاب القوى|الألعاب الأولمبية|الألعاب الآسيوية|"
    r"سياس|انتخاب|ترامب|بايدن|غزة|أسهم|سهم|بورصة|مستثمر|فيلم|مسلسل|دراما|أغنية|فنان|شات جي بي تي|جوجل كروم|تبويب|دراسة|المدارس|طقس|زلزال|عملات رقمية|بيتكوين", re.I)
TRUSTED_SRC = re.compile(
    r"\b(ign|gamespot|eurogamer|polygon|kotaku|vgc|videogameschronicle|gamesradar|game informer|pc gamer|rock paper shotgun|"
    r"push square|pure xbox|pure nintendo|xbox wire|nintendo life|pocket gamer|toucharcade|pcgamesn|gamesindustry\.biz|destructoid|"
    r"gematsu|insider gaming|gamerant|dexerto|vg247|the gamer|playstation blog|nintendo|xbox)\b"
    r"|سعودي جيمر|saudi gamer|تروجيمنج|true ?gaming|IGN الشرق", re.I)


def on_topic(title, summary, source, spec):
    """True only for games / games-company / PC-hardware-company news."""
    trusted = bool(spec.get("trusted") or TRUSTED_SRC.search(source or ""))
    text = f"{title} {summary}" if trusted else title      # untrusted sources must say it in the headline itself
    if DENY_HARD.search(f"{title} {summary}"):
        return False
    topical = bool(CORE.search(text) or COMPANY.search(text) or HARDWARE.search(text))
    core = bool(CORE.search(text) or COMPANY.search(text))
    soft = bool(DENY_SOFT.search(text))
    if soft and (not core or not trusted):
        return False                      # e.g. "Nvidia stock jumps", football "game", school/election news that merely mentions games
    if topical:
        return True
    return trusted and not soft           # trusted gaming outlets: game titles our lists do not know


# --------------------------------------------------------------------- main
def load_feed(spec, lang):
    t0 = time.time()
    url = gnews_url(spec["gnews"], lang) if spec.get("gnews") else spec["url"]
    res = {"name": spec["name"], "url": url, "ok": False, "items": [], "error": "", "ms": 0}
    for attempt in range(3):                         # Google News sometimes answers 503 under load: wait and retry
        try:
            items = parse_feed(http_get(url))
            res["items"] = items
            res["ok"] = bool(items)
            res["error"] = "" if items else "no items"
            break
        except Exception as e:                       # one bad feed must never stop the run
            res["error"] = f"{type(e).__name__}: {str(e)[:120]}"
            code = getattr(e, "code", 0)
            if attempt < 2 and (code in (429, 500, 502, 503, 504) or isinstance(e, (TimeoutError, OSError)) and not code):
                time.sleep(3 + attempt * 4 + (hash(url) % 3))
                continue
            break
    res["ms"] = int((time.time() - t0) * 1000)
    res["spec"] = spec
    return res



OG_RE = re.compile(r"<meta[^>]+(?:property|name)=[\"'](?:og:image|twitter:image)[\"'][^>]*>", re.I)
CT_RE = re.compile(r"content=[\"']([^\"']+)[\"']", re.I)


def page_image(url):
    """Read only the first 150 KB of an article and return its og:image (the publisher's own preview image)."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "text/html,*/*", "Accept-Encoding": "gzip"})
        with urllib.request.urlopen(req, timeout=8) as r:
            data = r.read(150_000)
            if r.headers.get("Content-Encoding") == "gzip" or data[:2] == b"\x1f\x8b":
                data = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(data)   # tolerates a truncated stream
        head = data.decode("utf-8", "ignore")
        for m in OG_RE.finditer(head):
            c = CT_RE.search(m.group(0))
            if c:
                u = https(urllib.parse.urljoin(url, html.unescape(c.group(1))))
                if u:
                    return u
    except Exception:
        return ""
    return ""


def enrich_images(items, limit=70):
    todo = [i for i in items if (not i["image"] or looks_small(i["image"])) and "news.google.com" not in i["url"]][:limit]   # missing OR thumbnail-sized
    if not todo:
        return 0
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for it, img in zip(todo, ex.map(lambda i: page_image(i["url"]), todo)):
            if img:
                it["image"] = img                    # the publisher's own og:image is the full-size picture
    return sum(1 for i in todo if i["image"] and not looks_small(i["image"]))


def build(lang, feeds, cfg, now):
    with cf.ThreadPoolExecutor(max_workers=10) as ex:
        results = list(ex.map(lambda s: load_feed(s, lang), feeds))
    cutoff = now - timedelta(days=cfg["max_age_days"])
    seen_u, seen_t, per_src, out = set(), set(), {}, []
    dropped = 0
    for r in results:
        spec = r["spec"]
        taken = 0
        for it in sorted(r["items"], key=lambda i: i["date"] or now, reverse=True):
            if taken >= cfg["per_feed_cap"]:
                break
            d = it["date"] or now
            if d < cutoff or d > now + timedelta(hours=2):
                continue
            title, source = it["title"], (it["source"] or spec["name"])
            if "news.google.com" in it["link"] and " - " in title:   # "Headline - Publisher"
                head, _, pub = title.rpartition(" - ")
                title, source = head.strip(), (it["source"] or pub.strip())
            if re.match(r"https?://", source or ""):          # some feeds put a URL in <source>: use the outlet name instead
                source = spec["name"]
            link = it["link"].strip()
            if not link.startswith(("http://", "https://")):
                continue
            ku, kt = norm_url(link), norm_title(title)
            if ku in seen_u or kt in seen_t or len(kt) < 8:
                continue
            if per_src.get(source, 0) >= cfg["per_source_cap"]:
                continue
            if not on_topic(title, it["summary"], source, spec):
                dropped += 1
                continue
            primary, tags = classify(f"{title} {it['summary']}", spec.get("category"))
            seen_u.add(ku); seen_t.add(kt)
            per_src[source] = per_src.get(source, 0) + 1
            taken += 1
            out.append({
                "id": hashlib.sha1(ku.encode()).hexdigest()[:12],
                "title": title,
                "url": link,
                "source": source,
                "category": primary,
                "tags": tags,
                "published": d.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "image": https(it["image"]),
                "summary": it["summary"],
            })
    out.sort(key=lambda i: i["published"], reverse=True)
    out = out[:cfg["max_items"] + 60]                       # a wider pool: stories without a usable picture are dropped below
    got = enrich_images(out, limit=120)
    with_img = [i for i in out if i["image"] and not looks_small(i["image"])]
    if len(with_img) >= 30:                                 # every story shows a real picture whenever we can afford it
        out = with_img
    out = out[:cfg["max_items"]]
    print(f"  [{lang}] off-topic items dropped: {dropped}; images added from article pages: {got}")
    health = [{"name": r["name"], "url": r["url"], "ok": r["ok"], "count": len(r["items"]),
               "ms": r["ms"], "error": r["error"]} for r in results]
    return out, health


def selftest():
    cases = [
        ("Elden Ring DLC sells 5 million copies", "", "IGN", {}, True),
        ("Nvidia unveils RTX 5090 Super with 32GB memory", "", "Tom's Hardware", {}, True),
        ("AMD Ryzen 9 9950X3D2 benchmark leaks", "", "VideoCardz", {}, True),
        ("Ubisoft delays next Assassin's Creed", "", "Reuters", {}, True),
        ("PlayStation Plus November 2026 lineup revealed", "", "Push Square", {}, True),
        ("إنفيديا تكشف عن كرت شاشة جديد للاعبين", "", "عالم التقنية", {}, True),
        ("مايكروسوفت تعلن موعد إكس بوكس جيم باس الجديد", "", "Saudi Gamer", {}, True),
        ("Nvidia stock jumps after earnings", "", "CNBC", {}, False),
        ("Real Madrid beat Barcelona in a thrilling football game", "", "DAZN", {}, False),
        ("Best online casino slots bonus", "", "Spam", {}, False),
        ("Trump signs new tariff order on chips", "", "Reuters", {}, False),
        ("مباراة الهلال والنصر في الدوري السعودي", "", "صدى البلد", {}, False),
        ("ألعاب القوى: نتائج بطولة آسيا", "", "اليوم السابع", {}, False),
        ("New Hollywood movie review", "", "Polygon", {"trusted": True}, False),
        ("Hollow Knight Silksong update 1.2 patch notes", "", "Kotaku", {"trusted": True}, True),
        ("Buy cheap game gold fast delivery", "", "MMOEXP", {}, False),
        ("أيام الدراسة أربعة أيام: يخشى الآباء أن تؤثر على ألعاب الأطفال", "", "Vietnam.vn", {}, False),
        ("Total War: Warhammer 4 DLC announced", "", "Some Site", {}, True),
        ("كيف تمنع شركات الذكاء الاصطناعي من استخدام بياناتك", "", "عرب هاردوير", {}, False),
        ("إضافة ChatGPT لجوجل كروم تقرأ تبويباتك", "", "عرب هاردوير", {}, False),
        ("أيام الدراسة أربعة أيام في الأسبوع", "ألعاب وأنشطة", "Vietnam.vn", {}, False),
        ("NVIDIA تنفي إيقاف إنتاج RTX 5090", "", "عرب هاردوير", {}, True),
        ("مطوّر Silent Hill يعتزم مواصلة إصدار الألعاب", "", "IGN الشرق الأوسط", {"trusted": True}, True),
    ]
    bad = 0
    for t, sm, src, spec, want in cases:
        got = on_topic(t, sm, src, spec)
        if got != want:
            bad += 1
            print("FAIL", want, got, t)
    print("selftest:", "ok" if not bad else f"{bad} failed", f"({len(cases)} cases)")
    sys.exit(1 if bad else 0)


def main():
    if "--selftest" in sys.argv:
        selftest()
    ap = argparse.ArgumentParser()
    ap.add_argument("--feeds", default=str(pathlib.Path(__file__).with_name("feeds.json")))
    ap.add_argument("--out", default="site")
    a = ap.parse_args()

    conf = json.loads(pathlib.Path(a.feeds).read_text(encoding="utf-8"))
    cfg = conf["settings"]
    out_dir = pathlib.Path(a.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    now = datetime.now(timezone.utc)
    status, ok = {}, True

    for lang, feeds in conf["feeds"].items():
        items, health = build(lang, feeds, cfg, now)
        counts = {}
        for i in items:
            counts[i["category"]] = counts.get(i["category"], 0) + 1
        payload = {"generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"), "lang": lang,
                   "count": len(items), "counts": counts, "items": items}
        (out_dir / f"news-{lang}.json").write_text(
            json.dumps(payload, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
        status[lang] = {"count": len(items), "counts": counts, "feeds": health}
        print(f"\n[{lang}] {len(items)} items  {counts}")
        for h in health:
            mark = "OK  " if h["ok"] else "FAIL"
            print(f"  {mark} {h['name'][:22]:22} {h['count']:3} items {h['ms']:5} ms  {h['error']}")
        if len(items) < cfg["min_items_to_publish"]:
            print(f"  !! only {len(items)} items for '{lang}' (< {cfg['min_items_to_publish']})")
            ok = False

    (out_dir / "status.json").write_text(json.dumps(
        {"generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"), **status},
        ensure_ascii=False, indent=1), encoding="utf-8")
    (out_dir / "index.html").write_text(
        "<!doctype html><meta charset=utf-8><title>Playora news feed</title>"
        "<p>JSON feeds: <a href=news-en.json>news-en.json</a> · <a href=news-ar.json>news-ar.json</a>"
        " · <a href=status.json>status.json</a></p>", encoding="utf-8")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
