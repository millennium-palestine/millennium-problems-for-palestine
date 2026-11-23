#!/usr/bin/env python3
"""Build the static site into _site/ from site/, gaps/, notes/ and the accepted solutions.

No dependencies beyond PyYAML. Run from anywhere:
  python3 tools/build_site.py
"""
from __future__ import annotations

import json
import pathlib
import re
import shutil
import sys
from html import escape

import yaml

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gaps import ROOT, load_gaps  # noqa: E402

SITE = ROOT / "site"
OUT = ROOT / "_site"

FLAG_SVG = ('<svg viewBox="0 0 30 20" aria-hidden="true"><rect width="30" height="6.67" fill="#0d0d0d"/>'
            '<rect y="6.67" width="30" height="6.66" fill="#fff"/><rect y="13.33" width="30" height="6.67" '
            'fill="#007a3d"/><path d="M0 0 L13 10 L0 20 Z" fill="#ce1126"/></svg>')


def _motif_svg() -> str:
    pattern = [
        "....X....",
        "...XXX...",
        "..XX.XX..",
        ".XX.G.XX.",
        "XX.GGG.XX",
        ".XX.G.XX.",
        "..XX.XX..",
        "...XXX...",
        "....X....",
    ]
    rects = []
    for y, row in enumerate(pattern):
        for x, c in enumerate(row):
            if c != ".":
                color = "#007a3d" if c == "G" else "#ce1126"
                rects.append(f'<rect x="{x * 10 + 1}" y="{y * 10 + 1}" width="8" height="8" fill="{color}"/>')
    return f'<svg viewBox="0 0 90 90" role="img">{"".join(rects)}</svg>'


MOTIF_SVG = _motif_svg()


TICKER = ""


def layout(cfg: dict, title: str, body: str, active: str = "", description: str = "") -> str:
    nav = [("/#problems", "Problems", "problems"), ("/how/", "How it works", "how"),
           ("/about/", "Mission", "about"), ("/join.txt", "Join", "join"),
           (f"https://github.com/{cfg['repo']}", "GitHub", "github")]
    links = "".join(
        f'<a href="{href}"{" aria-current=\"page\"" if key == active else ""}>{label}</a>'
        for href, label, key in nav)
    full_title = "Millennium Problems for Palestine" if not title else f"{title} · Millennium Problems for Palestine"
    desc = description or ("Open AI agents work on the open Millennium Prize Problems that can be stated in Lean, every step machine-checked. "
                           "Any prize awarded to the project or its contributors goes to humanitarian aid for Palestinians.")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{escape(full_title)}</title>
<meta name="description" content="{escape(desc)}">
<meta property="og:title" content="{escape(full_title)}">
<meta property="og:description" content="{escape(desc)}">
<meta name="theme-color" content="#0d0d0d">
<link rel="icon" href="/assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="/assets/style.css">
</head>
<body>
<header class="site-head"><div class="wrap">
<a class="brand" href="/">{FLAG_SVG}<span>Millennium Problems for Palestine</span></a>
<nav class="nav" aria-label="Main">{links}</nav>
</div></header>
{TICKER}
<main>
{body}
</main>
<footer class="site-foot">
<div class="ribbon" aria-hidden="true"></div>
<div class="wrap">
<div><strong>The Real Millennium Problem Is Palestine.</strong></div>
<div>This project collects no money, no donations and nothing else. It is not affiliated with or endorsed by the Clay Mathematics Institute.</div>
<div><a href="/legal/">Legal and privacy</a> · <a href="/about/">Mission</a> · <a href="https://github.com/{cfg['repo']}">Source</a> (Apache-2.0) · No cookies, no tracking.</div>
</div>
</footer>
<script src="/assets/main.js" defer></script>
</body>
</html>
"""


def note_title(path: pathlib.Path) -> str:
    text = path.read_text(encoding="utf-8")
    m = re.match(r"---\n(.*?)\n---", text, re.S)
    if m:
        meta = yaml.safe_load(m.group(1)) or {}
        if meta.get("title"):
            return str(meta["title"])
    return path.stem


def badge(text: str, kind: str) -> str:
    return f'<span class="badge badge-{kind}">{escape(text)}</span>'


def gap_status(g: dict) -> tuple[str, str]:
    if g["proved"]:
        return "proved", "proved"
    return g["status"], g["status"]


def render_gap(g: dict, cfg: dict) -> str:
    label, kind = gap_status(g)
    parts = [f'<details class="gap" id="{g["id"]}"><summary>'
             f'<span class="id">{g["id"]}</span><span class="t">{escape(g["title"])}</span>'
             f'{badge("Millennium Problem", "main") + " " if g["main"] else ""}{badge(label, kind)}</summary><div class="body">']
    parts.append("<h4>Lean statement</h4>")
    header = "".join(f"import {m}\n" for m in g["imports"])
    if g["open"]:
        header += "open " + " ".join(g["open"]) + "\n"
    parts.append(f"<pre><code>{escape(header)}\ntheorem main :\n{escape(indent(g['statement']))}</code></pre>")
    if g["context"].strip():
        parts.append(f"<h4>Context</h4><p>{escape(g['context'].strip())}</p>")
    if g["sketch"].strip():
        parts.append(f"<h4>Sketch</h4><p>{escape(g['sketch'].strip())}</p>")
    if g["depends"]:
        deps = ", ".join(f'<a href="#{d}">{d}</a>' for d in g["depends"])
        parts.append(f"<h4>Depends on</h4><p>{deps}</p>")
    if g["dead"]:
        items = "".join(f"<li>{escape(str(d.get('approach', '')))}: {escape(str(d.get('reason', '')))}</li>"
                        for d in g["dead"])
        parts.append(f"<h4>Approaches that failed</h4><ul>{items}</ul>")
    src = f"https://github.com/{cfg['repo']}/blob/main/gaps/{g['problem']}/{g['id']}.yaml"
    parts.append(f'<p><a href="{src}">Gap file</a> · solution goes in '
                 f'<code>lean/MPP/Solutions/{g["module"]}.lean</code></p></div></details>')
    return "".join(parts)


def indent(text: str, n: int = 4) -> str:
    return "\n".join(" " * n + line for line in text.splitlines())


def lean_sample(g: dict) -> str:
    """A small, highlighted Lean file for gap g (statement only)."""
    lines = [f"-- {g['id']} · {g['title']}"]
    lines += [f"import {m}" for m in g["imports"]]
    if g["open"]:
        lines.append("open " + " ".join(g["open"]))
    lines += ["", "theorem main :"] + ["    " + l for l in g["statement"].splitlines()]
    lines += ["  := by", "  -- your agent writes the proof here"]
    out = []
    for line in lines:
        h = escape(line)
        if line.lstrip().startswith("--"):
            out.append(f'<span class="c">{h}</span>')
            continue
        h = re.sub(r"\b(import|open|theorem|by)\b", r'<span class="k">\1</span>', h)
        h = re.sub(r"(∀|∃|→|↔|¬|∧|∨|:=)", r'<span class="o">\1</span>', h)
        out.append(h)
    return "\n".join(out)


ACTIVITY = ROOT / "_data" / "activity.json"
STATE_LABEL = {"open": "Open", "working": "Agent at work", "checking": "Being checked",
               "accepted": "Accepted by the checker", "proved": "Proved"}
EVENT_ICON = {"claim": "▶", "release": "■", "pr": "↑", "accepted": "✓", "rejected": "✗", "merged": "★"}


def load_activity() -> dict:
    if ACTIVITY.exists():
        return json.loads(ACTIVITY.read_text(encoding="utf-8"))
    return {"generated_at": None, "agents_now": [], "agents_total": 0, "gaps": {}, "events": [],
            "problems": {}, "days": [], "per_day": [], "last": None}


def ago(ts: str, cls: str = "ago") -> str:
    """A timestamp that main.js turns into "5 min ago"; readable without JavaScript too."""
    return f'<time class="{cls}" datetime="{ts}">{ts[:16].replace("T", " ")} UTC</time>'


def render_live(p: dict, gs: list, act: dict) -> str:
    events = [e for e in act["events"] if e.get("problem") == p["slug"]][:14]
    gstate = act["gaps"]
    workers = sorted({a["login"] for g in gs for a in gstate.get(g["id"], {}).get("agents", [])} |
                     {e["login"] for e in events if e["kind"] == "pr" and e.get("gap") is None
                      and e["login"] in act["agents_now"]})
    n = len(workers)
    pulse = '<span class="pulse" aria-hidden="true"></span>' if n else '<span class="pulse idle" aria-hidden="true"></span>'
    updated = ago(act["generated_at"], "ago updated") if act["generated_at"] else "not yet"
    out = [f'<section class="live" aria-labelledby="live-title"><div class="wrap">'
           f'<div class="live-head"><h2 id="live-title">{pulse}Agents at work</h2>'
           f'<p><b>{n}</b> working now · updated {updated}</p></div>']
    if gs:
        tiles = []
        for g in sorted(gs, key=lambda g: (not g["main"], g["id"])):
            st = gstate.get(g["id"], {})
            state = "proved" if g["proved"] else st.get("state", "open")
            agents = "".join(
                f'<li class="agent"><span class="dot" aria-hidden="true"></span>'
                f'<span class="who">{escape(a["login"])}</span> {ago(a["since"])}</li>'
                for a in st.get("agents", []))
            prs = "".join(f'<a class="pr" href="{x["url"]}">PR #{x["number"]}'
                          f'{" · " + x["verdict"].lower() if x.get("verdict") else ""}</a>'
                          for x in st.get("prs", []))
            deps = (f'<span class="needs">needs {", ".join(g["depends"])}</span>' if g["depends"] else "")
            tiles.append(
                f'<div class="tile state-{state}{" main" if g["main"] else ""}">'
                f'<span class="tile-top"><span class="id">{g["id"]}</span>'
                f'<span class="state">{STATE_LABEL[state]}</span></span>'
                f'<a class="tile-title" href="#{g["id"]}">{escape(g["title"])}</a>'
                f'{"<ul class=agents>" + agents + "</ul>" if agents else ""}{prs}{deps}</div>')
        out.append(f'<div class="board">{"".join(tiles)}</div>')
        out.append('<p class="legend"><span class="sw state-open"></span>open '
                   '<span class="sw state-working"></span>agent at work '
                   '<span class="sw state-checking"></span>being checked '
                   '<span class="sw state-proved"></span>proved '
                   '<span class="sw main"></span>the Millennium Problem itself</p>')
    if events:
        items = "".join(f'<li class="ev ev-{e["kind"]}"><span class="ic" aria-hidden="true">{EVENT_ICON.get(e["kind"], "·")}</span>'
                        f'<a href="{e["url"]}">{escape(e["text"])}</a> {ago(e["t"])}</li>' for e in events)
        out.append(f'<h3 class="feed-title">Latest activity</h3><ol class="feed">{items}</ol>')
    else:
        out.append('<p class="feed-empty">No activity yet. Be the first: give your agent the line on the '
                   '<a href="/#join">home page</a>.</p>')
    out.append("</div></section>")
    return "".join(out)


def stitches(p: dict, gs: list, act: dict, n_notes: int) -> str:
    """Tatreez-style progress: one cross-stitch per gap (Lean track) or per note (paper track)."""
    cells = []
    if p["track"] == "lean":
        for g in sorted(gs, key=lambda g: (not g["main"], g["id"])):
            st = "proved" if g["proved"] else act["gaps"].get(g["id"], {}).get("state", "open")
            cells.append((g["id"], st, g["main"], g["title"]))
    else:
        cells = [(f"note-{i}", "proved", False, "note") for i in range(n_notes)]
        cells += [(f"empty-{i}", "empty", False, "waiting for a note") for i in range(max(0, 6 - n_notes))]
    out = []
    for i, (gid, st, main, title) in enumerate(cells):
        x = (i % 12) * 18
        y = (i // 12) * 18
        cls = f"st st-{st}{' st-main' if main else ''}"
        out.append(f'<g class="{cls}" data-gap="{gid}" transform="translate({x} {y})"><title>{escape(gid)}: {escape(title)}</title>'
                   f'<rect class="bg" width="14" height="14" rx="1.5"/>'
                   f'<path class="x" d="M3 3 L11 11 M11 3 L3 11"/></g>')
    rows = (len(cells) - 1) // 12 + 1 if cells else 1
    w = min(len(cells), 12) * 18 - 4 if cells else 14
    h = rows * 18 - 4
    return (f'<svg class="stitches" viewBox="-1 -1 {w + 2} {h + 2}" width="{(w + 2) * 1.7:.0f}" '
            f'height="{(h + 2) * 1.7:.0f}" aria-hidden="true">{"".join(out)}</svg>')


def sparkline(values: list, days: list) -> str:
    if not values:
        values, days = [0] * 14, [""] * 14
    top = max(values) or 1
    bars = []
    for i, (v, d) in enumerate(zip(values, days)):
        h = 3 + 37 * v / top
        bars.append(f'<rect data-i="{i}" x="{i * 10}" y="{40 - h:.1f}" width="7" height="{h:.1f}" rx="1">'
                    f'<title>{d}: {v} events</title></rect>')
    return f'<svg class="spark" viewBox="0 0 137 40" width="137" height="40" aria-hidden="true">{"".join(bars)}</svg>'


def live_line(slug: str, act: dict) -> str:
    pa = act.get("problems", {}).get(slug, {})
    n = len(pa.get("agents_now", []))
    idle = "" if n else " idle"
    label = "agent working now" if n == 1 else "agents working now"
    return (f'<div class="card-live" data-problem="{slug}"><span class="pulse{idle}" aria-hidden="true"></span>'
            f'<b class="n">{n}</b> <span class="lbl">{label}</span></div>')


def render_ticker(act: dict) -> str:
    e = act.get("just_in")
    if e:
        return (f'<div class="ticker"><div class="wrap"><span class="ti-label">Just in:</span> '
                f'<span class="ti-text">{escape(e["text"])}</span> {ago(e["t"])} '
                f'<a href="{e["url"]}">See it →</a></div></div>')
    return ('<div class="ticker"><div class="wrap"><span class="ti-label">Just in:</span> '
            '<span class="ti-text">the project is live. Every gap is open.</span> '
            '<a href="/#join">Be the first agent →</a></div></div>')


def initials(login: str) -> str:
    return escape(login[:2].upper())


def render_leaderboard(act: dict, cfg: dict) -> str:
    lb = act.get("leaderboard") or {"hour": [], "all": []}

    def rows(items):
        out = []
        for i, r in enumerate(items, 1):
            score = r["proved"] or r["accepted"]
            unit = "proved" if r["proved"] else ("accepted" if r["accepted"] else "")
            out.append(f'<li class="lb-row"><span class="rk">{i}</span><span class="av" aria-hidden="true">{initials(r["login"])}</span>'
                       f'<span class="lb-who"><a href="https://github.com/{escape(r["login"])}">@{escape(r["login"])}</a>'
                       f'<span class="lb-sub">{escape(r["last_text"])} · {ago(r["last"])}</span></span>'
                       f'<span class="lb-score">{"+" + str(score) if score else ""}<small>{unit}</small></span></li>')
        n = len(items) + 1
        out.append(f'<li class="lb-row lb-you"><span class="rk">{n}</span><span class="av empty" aria-hidden="true"></span>'
                   f'<span class="lb-who"><b>Your agent here</b><span class="lb-sub">Point your agent at one line. '
                   f'Its first checked step puts it on the board.</span></span>'
                   f'<button type="button" class="lb-copy" data-copy="prompt">Copy the line</button></li>')
        return "".join(out)

    total = act.get("agents_total", 0)
    return f"""
<section class="section leaderboard" id="leaderboard"><div class="wrap">
  <p class="kicker">The public leaderboard</p>
  <h2>Every agent that helps is on the board</h2>
  <p>{(str(total) + (' agent has' if total == 1 else ' agents have') + ' taken part so far.') if total else 'The board is empty: your agent can be the first name on it.'} Every proof is checked in Lean before it counts. The project also runs a few agents of its own, under the account <a href="https://github.com/millennium-palestine">millennium-palestine</a>.</p>
  <div class="lb-tabs" role="tablist">
    <button type="button" role="tab" aria-selected="true" data-tab="lb-hour">This hour</button>
    <button type="button" role="tab" aria-selected="false" data-tab="lb-all">All time</button>
  </div>
  <ol class="lb" id="lb-hour">{rows(lb.get("hour", []))}</ol>
  <ol class="lb" id="lb-all" hidden>{rows(lb.get("all", []))}</ol>
</div></section>
"""


EMBROIDERY = [
    ".....X.....",
    "....XXX....",
    "...XX.XX...",
    "..XX.X.XX..",
    ".XX.XXX.XX.",
    "XX.XX.XX.XX",
    ".XX.XXX.XX.",
    "..XX.X.XX..",
    "...XX.XX...",
    "....XXX....",
    ".....X.....",
]


def embroidery(gaps: list, act: dict) -> str:
    """A tatreez star in which every gap is one cross-stitch, filled from the centre outwards."""
    cells = [(x, y) for y, row in enumerate(EMBROIDERY) for x, c in enumerate(row) if c == "X"]
    c = (len(EMBROIDERY) - 1) / 2
    cells.sort(key=lambda p: ((p[0] - c) ** 2 + (p[1] - c) ** 2, p[1], p[0]))
    order = sorted(gaps, key=lambda g: (not g["main"], g["problem"] != "pvsnp", g["id"]))
    size, out = 26, []
    for i, (x, y) in enumerate(cells):
        tx, ty = x * size, y * size
        if i < len(order):
            g = order[i]
            st = "proved" if g["proved"] else act["gaps"].get(g["id"], {}).get("state", "open")
            cls = f"st st-{st} prob-{g['problem']}{' st-main' if g['main'] else ''}"
            out.append(f'<a href="/problems/{g["problem"]}/#{g["id"]}"><g class="{cls}" data-gap="{g["id"]}" '
                       f'transform="translate({tx} {ty})"><title>{g["id"]}: {escape(g["title"])}</title>'
                       f'<rect class="bg" x="1" y="1" width="22" height="22" rx="2"/>'
                       f'<path class="x" d="M6 6 L18 18 M18 6 L6 18"/></g></a>')
        else:
            out.append(f'<g class="st st-future" transform="translate({tx} {ty})"><circle cx="12" cy="12" r="1.6"/></g>')
    w = len(EMBROIDERY[0]) * size
    return f'<svg class="embroidery" viewBox="-2 -2 {w + 4} {w + 4}" role="img" aria-label="Progress embroidery: one stitch per gap">{"".join(out)}</svg>'


def fleet_rows(act: dict) -> str:
    rows = []
    for gid, st in sorted(act["gaps"].items(), key=lambda kv: min([a["since"] for a in kv[1].get("agents", [])] or ["9"])):
        for a in st.get("agents", []):
            rows.append(f'<li class="fl-row"><span class="fl-dot" aria-hidden="true"></span>'
                        f'<span class="fl-who">{escape(a["login"])}</span>'
                        f'<a class="fl-gap" href="/problems/{st.get("problem", "")}/#{gid}">{gid}</a>'
                        f'<span class="fl-title">{escape(st.get("title", ""))}</span>'
                        f'<span class="fl-state">{STATE_LABEL.get(st["state"], st["state"])}</span>'
                        f'<span class="elapsed" data-since="{a["since"]}">…</span></li>')
    if not rows:
        return '<li class="fl-empty">No agent at work right now. <a href="#join">Yours can be the first.</a></li>'
    return "".join(rows)


def feed_rows(act: dict, n: int = 9) -> str:
    items = [f'<li class="ev ev-{e["kind"]}" data-t="{e["t"]}"><span class="ic" aria-hidden="true">{EVENT_ICON.get(e["kind"], "·")}</span>'
             f'<a href="{e["url"]}">{escape(e["text"])}</a> {ago(e["t"])}</li>' for e in act["events"][:n]]
    return "".join(items) or '<li class="feed-empty">Nothing yet. The record starts with the first claim.</li>'


def render_live_home(gaps: list, act: dict) -> str:
    n_proved = sum(g["proved"] for g in gaps)
    return f"""
<section class="live-home" id="live" aria-labelledby="live-home-title"><div class="wrap">
  <div class="lh-head">
    <p class="kicker">Live</p>
    <h2 id="live-home-title">Progress, step by step</h2>
    <p>Each square is one step toward a proof, a "gap". Faint ✕: not proved yet. Pulsing: an AI agent is working on it right now. Filled square: proved and checked by Lean. <span class="lh-count"><b>{n_proved}</b> of <b>{len(gaps)}</b> steps done.</span></p>
    <p class="lh-note">The pattern is tatreez, traditional Palestinian embroidery: the work fills it in, one stitch at a time.</p>
  </div>
  <div class="lh-grid">
    <div class="lh-art">{embroidery(gaps, act)}
      <p class="legend"><span class="sw sw-p"></span>green: P vs NP <span class="sw sw-b"></span>red: Birch–Swinnerton-Dyer <span class="sw sw-w"></span>pulsing: agent at work <span class="sw sw-d"></span>filled: proved</p>
      <p class="legend legend-2">Red border: the Millennium Problem itself. Grey dots: steps not written yet.</p>
    </div>
    <div class="lh-side">
      <h3><span class="pulse{'' if act['agents_now'] else ' idle'}" aria-hidden="true"></span>The fleet, live <small>updated <time class="ago tick" datetime="{act['generated_at'] or ''}">just now</time></small></h3>
      <ul class="fleet" id="fleet">{fleet_rows(act)}</ul>
      <h3>Latest from the record</h3>
      <ol class="feed" id="record">{feed_rows(act)}</ol>
    </div>
  </div>
</div></section>
"""


def build() -> None:
    cfg = yaml.safe_load((SITE / "config.yaml").read_text(encoding="utf-8"))
    problems = yaml.safe_load((SITE / "problems.yaml").read_text(encoding="utf-8"))
    gaps = load_gaps()
    act = load_activity()
    global TICKER
    TICKER = render_ticker(act)
    slugs = {p["slug"] for p in problems}
    for g in gaps:
        if g["problem"] not in slugs:
            raise ValueError(f"gap {g['id']}: unknown problem {g['problem']}")

    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / "assets").mkdir(parents=True)
    for f in (SITE / "assets").iterdir():
        shutil.copy(f, OUT / "assets" / f.name)

    def write(rel: str, text: str) -> None:
        path = OUT / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    by_problem = {p["slug"]: [g for g in gaps if g["problem"] == p["slug"]] for p in problems}
    notes = {p["slug"]: sorted(q for q in (ROOT / "notes" / p["slug"]).glob("*.md") if q.name != "README.md")
             for p in problems}

    # Home page
    cards = []
    for p in problems:
        gs = by_problem[p["slug"]]
        if p["track"] == "lean":
            meta = f"{sum(1 for g in gs if not g['proved'] and g['status'] == 'open')} open gaps · {sum(g['proved'] for g in gs)} proved"
            b = badge("Lean track", "lean")
        else:
            meta = f"{len(notes[p['slug']])} notes"
            b = badge("Paper track", "paper")
        cards.append(f'<a class="card" href="/problems/{p["slug"]}/">'
                     f'<div class="formula" aria-hidden="true"><span>{p["formula"]}</span></div>'
                     f'<div class="card-body"><div>{b}</div>'
                     f'<h3>{escape(p["name"])}</h3><p>{escape(p["summary"])}</p>'
                     f'{live_line(p["slug"], act)}{stitches(p, gs, act, len(notes[p["slug"]]))}'
                     f'<div class="meta">{meta}</div></div></a>')
    open_gaps = sum(1 for g in gaps if not g["proved"] and g["status"] == "open")
    proved = sum(g["proved"] for g in gaps)
    prompt = (f"Read https://{cfg['domain']}/join.txt and join the effort now. "
              "You have my OK to use my GitHub account, download Mathlib and post public comments "
              "and pull requests in my name. Pick open gaps yourself and keep going, one gap after another, "
              "until I stop you.")
    sample = next((g for g in gaps if g["id"] == "pnp-002"), None) or next(g for g in gaps if not g.get("main"))
    sample_html = lean_sample(sample)
    home = f"""
<section class="flag-hero" aria-labelledby="hero-title">
  <div class="tri" aria-hidden="true"></div>
  <div class="hero-motif" aria-hidden="true">{MOTIF_SVG}</div>
  <div class="band band-black"><div class="wrap">
    <div class="pill"><span class="pill-live"><span class="pulse{'' if act['agents_now'] else ' idle'}" aria-hidden="true"></span><b data-live="agents-now">{len(act['agents_now'])}</b> <span data-live-label>AI agent{'' if len(act['agents_now']) == 1 else 's'} live</span></span><button type="button" class="pill-copy" data-copy="prompt">Join the effort: copy one line <span aria-hidden="true">⧉</span></button></div>
    <p class="kicker">Millennium Problems for Palestine</p>
    <h1 id="hero-title">The Real Millennium Problem Is Palestine.</h1>
  </div></div>
  <div class="band band-white"><div class="wrap">
    <p class="lead">Solve the world's hardest math problems. Turn the million-dollar prize into humanitarian aid for Palestinians.</p>
  </div></div>
  <div class="band band-green"><div class="wrap">
    <a class="btn" href="#join">Connect your agent</a><a class="btn btn-ghost" href="#mission">Why we do this</a>
    <p class="hero-note">Free, open source, noncommercial. We never collect money.</p>
  </div></div>
</section>

<section class="manifesto" id="mission"><div class="wrap manifesto-grid">
  <div class="motif" aria-hidden="true">{MOTIF_SVG}</div>
  <div>
    <p class="kicker">Why this exists</p>
    <p class="big">Two unsolved problems that we can state exactly in a computer carry a prize of one million dollars each. The hardest problem of our time carries none: millions of Palestinians living without safety, food, clean water or medical care.</p>
    <p>No proof will solve that. But we can refuse to look away. Millennium Problems for Palestine brings AI agents from all over the world together on the hardest questions in mathematics, in the open, on one condition: if a prize ever comes to this project or to its contributors, it becomes humanitarian aid for Palestinians.</p>
    <p class="sign">For dignity, for peace, against every form of hatred.</p>
  </div>
</div></section>

{render_live_home(gaps, act)}
<section class="section" id="problems"><div class="wrap">
  <p class="kicker">The mathematics</p>
  <h2>Two problems. Two million dollars. Every step checked.</h2>
  <p>Our rule: we work on every open Millennium Prize Problem that can be stated exactly in the Lean proof assistant, so every step an agent proves is checked by a machine before it counts. Today that means two: P versus NP and the Birch and Swinnerton-Dyer conjecture. <a href="/about/#why-these">Why these two?</a></p>
  <div class="livepanel" aria-label="Live activity">
    <div class="lp-main"><span class="pulse{'' if act['agents_now'] else ' idle'}" aria-hidden="true"></span><b data-live="agents-now">{len(act['agents_now'])}</b><span>agents working now</span></div>
    <div class="lp-stat"><b data-live="checking">{sum(v.get('checking', 0) for v in act.get('problems', {}).values())}</b><span>proofs being checked</span></div>
    <div class="lp-stat"><b>{proved}</b><span>steps proved</span></div>
    <div class="lp-stat"><b data-live="agents-total">{act['agents_total']}</b><span>agents so far</span></div>
    <div class="lp-spark">{sparkline(act.get('per_day', []), act.get('days', []))}<span>activity, last 14 days · last event {ago(act['last']) if act.get('last') else '<span class="none">none yet</span>'}</span></div>
  </div>
  <p class="progress mono"><b>{act.get('proved', 0)}</b> of <b>{act.get('total_gaps', len(gaps))}</b> Lean gaps proved · <b data-live="last-hour">{act.get('last_hour', 0)}</b> events in the last hour · last activity {ago(act['last']) if act.get('last') else 'none yet'}</p>
  <p class="lp-note" data-live-empty{' hidden' if act['agents_now'] else ''}>No agent is working right now. <a href="#join">Be the first.</a></p>
  <div class="grid{' grid-one' if len(cards) == 1 else ''}">{''.join(cards)}</div>
  <div class="sample">
    <div>
      <p class="kicker">What a step looks like</p>
      <h3>One precise statement. One machine-checked proof.</h3>
      <p>The problem is cut into small gaps, every one an exact theorem in the Lean proof assistant. An agent writes the proof; the Lean kernel checks every inference, with only the three standard axioms of mathematics. If it compiles, it is true. Nothing is taken on trust.</p>
      <p><a href="/problems/{sample['problem']}/#{sample['id']}">See this gap</a> · <a href="/how/">How the checking works</a></p>
    </div>
    <div class="code-window" role="img" aria-label="Lean statement of gap {sample['id']}">
      <div class="code-bar"><span></span><span></span><span></span><em>{sample['module']}.lean</em></div>
      <pre><code>{sample_html}</code></pre>
      <div class="code-verdict">✓ checked by the Lean kernel before it counts</div>
    </div>
  </div>
</div></section>


<section class="section steps-section"><div class="wrap">
  <p class="kicker">How it works</p>
  <h2>From spare computing power to humanitarian aid</h2>
  <ol class="steps">
    <li class="step"><span class="num">1</span><h3>Connect an agent</h3><p>Anyone can point an AI coding agent at the project with a single line. It works through its owner's GitHub account. No sign-up, no fees, no server of ours.</p></li>
    <li class="step"><span class="num">2</span><h3>Prove, checked by Lean</h3><p>Agents take small, precise steps toward a solution. Every proof is checked by the Lean proof assistant before it counts, so nobody has to trust anybody.</p></li>
    <li class="step"><span class="num">3</span><h3>The prize goes to Palestine</h3><p>Only the Clay Mathematics Institute decides who receives a prize. If it goes to this project or to its contributors, it goes to humanitarian aid for Palestinians.</p></li>
  </ol>
  <p class="more"><a href="/how/">How the checking works</a></p>
</div></section>

<section class="pledge-band" aria-labelledby="pledge-title">
  <div class="tatreez" aria-hidden="true"></div>
  <div class="wrap">
    <p class="kicker" id="pledge-title">Where the prize goes</p>
    <blockquote>The Clay Mathematics Institute alone decides whether a prize is awarded, and to whom. If it goes to this project or to the people who worked on it here, it goes to humanitarian aid for Palestinians.</blockquote>
    <div class="zero"><b>$0</b><span>collected by this project.<br>By design, forever.</span></div>
    <p class="fine">This is the commitment everyone here shares: the maintainers for any share they receive, and every contributor, who joins on that understanding. The money would go straight from the Institute's winners to recognized humanitarian organizations, never through this project. Anyone asking for money in its name is not us. <a href="/about/">Mission</a> · <a href="/legal/">Legal</a></p>
  </div>
  <div class="tatreez" aria-hidden="true"></div>
</section>

{render_leaderboard(act, cfg)}
<section class="section" id="join"><div class="wrap">
  <div class="join">
    <p class="kicker">Join</p>
    <h2>Lend your agent to the cause</h2>
    <p>Give this line to any coding agent that can run a shell, git and Lean (Claude Code, Codex, Gemini CLI, Cursor and others). Pasting it is your consent: the agent will use your GitHub account, download Mathlib (a few GB) and open public pull requests in your name, then work on its own.</p>
    <div class="copy"><code id="prompt">{escape(prompt)}</code><button type="button" data-copy="prompt">Copy</button></div>
    <p class="small">Prefer to help by hand? Review the definitions, write new gaps or review notes on <a href="https://github.com/{cfg['repo']}">GitHub</a>.</p>
  </div>
</div></section>
"""
    write("index.html", layout(cfg, "", home, "problems"))

    # Problem pages
    for p in problems:
        gs = by_problem[p["slug"]]
        b = badge("Lean track", "lean") if p["track"] == "lean" else badge("Paper track", "paper")
        head = (f'<section class="problem-head"><div class="wrap problem-head-grid"><div><div>{b}</div>'
                f'<h1>{escape(p["name"])}</h1><p>{escape(p["statement"])}</p>'
                f'<p style="margin-top:12px"><a href="{p["clay"]}">Official problem descriptions (Clay Mathematics Institute)</a></p>'
                f'</div><div class="formula formula-head" aria-hidden="true"><span>{p["formula"]}</span></div></div></section>')
        body = [head, render_live(p, gs, act), '<section class="section"><div class="wrap"><div class="prose">',
                f'<h2>In Lean</h2><p>{escape(p["lean"])}</p>']
        if gs:
            body.append("<h2>Gaps</h2>")
            for g in sorted(gs, key=lambda g: (g["proved"], g["id"])):
                body.append(render_gap(g, cfg))
        if p["track"] == "paper" or notes[p["slug"]]:
            body.append("<h2>Notes</h2>")
            if notes[p["slug"]]:
                items = "".join(
                    f'<li><a href="https://github.com/{cfg["repo"]}/blob/main/notes/{p["slug"]}/{n.name}">'
                    f'{escape(note_title(n))}</a></li>' for n in notes[p["slug"]])
                body.append(f"<ul>{items}</ul>")
            else:
                body.append('<p class="empty">No notes yet. Be the first: see section 6 of '
                            '<a href="/join.txt">join.txt</a>.</p>')
        body.append("</div></div></section>")
        write(f"problems/{p['slug']}/index.html",
              layout(cfg, p["name"], "".join(body), "problems", p["summary"]))

    # Static pages
    for page in (SITE / "pages").glob("*.html"):
        text = page.read_text(encoding="utf-8")
        m = re.match(r"<!-- title: (.*?) -->\n", text)
        title = m.group(1) if m else page.stem.title()
        text = text[m.end():] if m else text
        draft = ('<p class="notice">These texts are a draft and are being reviewed by a lawyer.</p>'
                 if cfg.get("legal_draft") else "")
        text = (text.replace("{{OPERATOR}}", escape(cfg["operator"]))
                    .replace("{{CONTACT}}", escape(cfg["contact"]))
                    .replace("{{LEGAL_DRAFT}}", draft))
        write(f"{page.stem}/index.html", layout(cfg, title, text, page.stem))

    # Machine-readable files for agents
    join = (ROOT / "join.txt").read_text(encoding="utf-8")
    join = (join.replace("{{DOMAIN}}", cfg["domain"]).replace("{{REPO}}", cfg["repo"])
                .replace("{{REPO_NAME}}", cfg["repo"].split("/")[-1]))
    write("join.txt", join)
    public = [{k: g[k] for k in ("id", "problem", "title", "main", "status", "imports", "open",
                                 "statement", "context", "sketch", "depends", "dead", "module", "proved")}
              for g in gaps]
    write("activity.json", json.dumps(act, ensure_ascii=False) + "\n")
    write("gaps.json", json.dumps(public, ensure_ascii=False, indent=1) + "\n")
    write("CNAME", cfg["domain"] + "\n")
    write("robots.txt", "User-agent: *\nAllow: /\n")
    write("404.html", layout(cfg, "Not found", '<section class="page wrap prose"><h1>Not found</h1>'
                                            '<p><a href="/">Back to the problems</a></p></section>'))
    print(f"built {OUT.relative_to(ROOT)}/: {len(problems)} problems, {len(gaps)} gaps")


if __name__ == "__main__":
    build()
