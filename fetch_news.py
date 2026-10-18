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
            if t in ("thumbnail", "content", "enclosure") and not it["image"]:
                u = c.get("url") or c.get("href")
                typ = (c.get("type") or c.get("medium") or "").lower()
                if u and (t == "thumbnail" or "image" in typ or re.search(r"\.(jpe?g|png|webp)(\?|$)", u, re.I)):
                    it["image"] = u
            if t == "group":                       # <media:group>
                for g in c:
                    if local(g.tag) in ("thumbnail", "content") and g.get("url") and not it["image"]:
                        it["image"] = g.get("url")
        if not it["image"]:
            for blob in html_blobs:
                m = IMG_RE.search(blob or "")
                if m:
                    it["image"] = m.group(1)
                    break
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


# --------------------------------------------------------------------- main
def load_feed(spec, lang):
    t0 = time.time()
    url = gnews_url(spec["gnews"], lang) if spec.get("gnews") else spec["url"]
    res = {"name": spec["name"], "url": url, "ok": False, "items": [], "error": "", "ms": 0}
    try:
        items = parse_feed(http_get(url))
        res["items"] = items
        res["ok"] = bool(items)
        if not items:
            res["error"] = "no items"
    except Exception as e:                           # one bad feed must never stop the run
        res["error"] = f"{type(e).__name__}: {str(e)[:120]}"
    res["ms"] = int((time.time() - t0) * 1000)
    res["spec"] = spec
    return res


def build(lang, feeds, cfg, now):
    with cf.ThreadPoolExecutor(max_workers=10) as ex:
        results = list(ex.map(lambda s: load_feed(s, lang), feeds))
    cutoff = now - timedelta(days=cfg["max_age_days"])
    seen_u, seen_t, per_src, out = set(), set(), {}, []
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
            link = it["link"].strip()
            if not link.startswith(("http://", "https://")):
                continue
            ku, kt = norm_url(link), norm_title(title)
            if ku in seen_u or kt in seen_t or len(kt) < 8:
                continue
            if per_src.get(source, 0) >= cfg["per_source_cap"]:
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
    out = out[:cfg["max_items"]]
    health = [{"name": r["name"], "url": r["url"], "ok": r["ok"], "count": len(r["items"]),
               "ms": r["ms"], "error": r["error"]} for r in results]
    return out, health


def main():
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
