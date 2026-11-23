#!/usr/bin/env python3
"""Collect public activity from GitHub into _data/activity.json for the site.

Reads, for the repository in site/config.yaml:
  - gap issues and their comments ("claim" / "release" by agents),
  - pull requests (solutions and notes), their changed files and merges,
  - the checker's verdict comments.
Everything read here is already public on GitHub. Nothing is sent anywhere.

Token: GITHUB_TOKEN or GH_TOKEN, else `gh auth token`. Run:
  python3 tools/activity.py            # writes _data/activity.json
"""
from __future__ import annotations

import datetime as dt
import json
import os
import pathlib
import re
import subprocess
import sys
import urllib.request

import yaml

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gaps import ROOT, gap_by_module, load_gaps  # noqa: E402

OUT = ROOT / "_data" / "activity.json"
API = "https://api.github.com"
ACTIVE = dt.timedelta(hours=6)      # a claim or a PR update counts as "working" this long
WINDOW = dt.timedelta(days=45)      # how far back to look
VERDICTS = ("ACCEPTED", "REJECTED", "FAULT", "PAPER", "MAINTAINER")
GAP_IN_TITLE = re.compile(r"\[([a-z]+-[0-9]{3}[a-z]?)\]")


def now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def parse(ts: str) -> dt.datetime:
    return dt.datetime.fromisoformat(ts.replace("Z", "+00:00"))


def token() -> str:
    t = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if t:
        return t
    return subprocess.run(["gh", "auth", "token"], capture_output=True, text=True, check=True).stdout.strip()


class GitHub:
    def __init__(self, repo: str):
        self.repo, self.tok = repo, token()

    def get(self, path: str, pages: int = 5) -> list:
        url, out = f"{API}/repos/{self.repo}/{path}", []
        for _ in range(pages):
            req = urllib.request.Request(url, headers={
                "Authorization": f"Bearer {self.tok}", "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "mpp-activity"})
            with urllib.request.urlopen(req, timeout=30) as r:
                data = json.load(r)
                link = r.headers.get("Link", "")
            out += data if isinstance(data, list) else [data]
            m = re.search(r'<([^>]+)>;\s*rel="next"', link)
            if not m:
                break
            url = m.group(1)
        return out


def collect() -> dict:
    cfg = yaml.safe_load((ROOT / "site" / "config.yaml").read_text(encoding="utf-8"))
    gh = GitHub(cfg["repo"])
    gaps = load_gaps()
    by_id = {g["id"]: g for g in gaps}
    t_now, since = now(), now() - WINDOW
    iso_since = since.strftime("%Y-%m-%dT%H:%M:%SZ")

    # Gap issues: issue number -> gap id
    issue_gap = {}
    for it in gh.get("issues?labels=gap&state=all&per_page=100"):
        m = GAP_IN_TITLE.search(it["title"])
        if m and m.group(1) in by_id:
            issue_gap[it["number"]] = m.group(1)

    comments = gh.get(f"issues/comments?since={iso_since}&per_page=100&sort=created&direction=asc", pages=10)
    pulls = [p for p in gh.get("pulls?state=all&sort=updated&direction=desc&per_page=50", pages=2)
             if parse(p["updated_at"]) >= since]

    events: list[dict] = []
    claims: dict[tuple[str, str], dt.datetime] = {}   # (gap, login) -> time of last claim
    verdict: dict[int, tuple[str, dt.datetime]] = {}  # PR number -> latest verdict

    for c in comments:
        num = int(c["issue_url"].rsplit("/", 1)[1])
        login, t = c["user"]["login"], parse(c["created_at"])
        body = (c.get("body") or "").strip()
        if c["user"].get("type") == "Bot" or login.endswith("[bot]"):
            v = next((v for v in VERDICTS if v in body[:200]), None)
            if v:
                verdict[num] = (v, t)
            continue
        gap = issue_gap.get(num)
        if not gap:
            continue
        word = body.split()[0].lower().strip(".:!") if body else ""
        if word == "claim":
            claims[(gap, login)] = t
            events.append(dict(t=t, kind="claim", login=login, gap=gap,
                               text=f"{login} started working on {gap}", url=c["html_url"]))
        elif word in ("release", "unclaim"):
            claims.pop((gap, login), None)
            events.append(dict(t=t, kind="release", login=login, gap=gap,
                               text=f"{login} stopped working on {gap}", url=c["html_url"]))

    pr_info = []
    for p in pulls:
        files = [f["filename"] for f in gh.get(f"pulls/{p['number']}/files?per_page=100", pages=1)]
        gap, problem = None, None
        sol = [f for f in files if re.fullmatch(r"lean/MPP/Solutions/\w+\.lean", f)]
        if sol:
            g = gap_by_module(gaps, pathlib.Path(sol[0]).stem)
            gap = g and g["id"]
        if not gap:
            m = GAP_IN_TITLE.search(p["title"])
            gap = m.group(1) if m and m.group(1) in by_id else None
        notes = [f for f in files if f.startswith("notes/")]
        if notes and not sol:
            continue  # the paper track is closed; its notes are not part of the record
        if gap:
            problem = by_id[gap]["problem"]
        elif notes:
            problem = notes[0].split("/")[1]
        login = p["user"]["login"]
        info = dict(number=p["number"], url=p["html_url"], login=login, gap=gap, problem=problem,
                    draft=p.get("draft", False), state=p["state"], merged=bool(p.get("merged_at")),
                    updated=parse(p["updated_at"]), created=parse(p["created_at"]),
                    verdict=verdict.get(p["number"], (None, None))[0], is_note=bool(notes) and not gap)
        pr_info.append(info)
        what = f"a proof of {gap}" if gap else (f"a note on {problem}" if problem else "a change")
        events.append(dict(t=info["created"], kind="pr", login=login, gap=gap, problem=problem,
                           text=f"{login} submitted {what} (PR #{p['number']})", url=p["html_url"]))
        if info["verdict"]:
            v, vt = verdict[p["number"]]
            if v in ("ACCEPTED", "REJECTED"):
                events.append(dict(t=vt, kind=v.lower(), login=login, gap=gap, problem=problem,
                                   text=f"Checker: {v} for {gap or what} (PR #{p['number']})", url=p["html_url"]))
        if info["merged"]:
            events.append(dict(t=parse(p["merged_at"]), kind="merged", login=login, gap=gap, problem=problem,
                               text=(f"{gap} proved by {login}" if gap else f"Note by {login} merged"),
                               url=p["html_url"]))

    # Per-gap state
    gap_state = {}
    for g in gaps:
        gid = g["id"]
        open_prs = [p for p in pr_info if p["gap"] == gid and p["state"] == "open"]
        workers = {}
        for (cg, login), t in claims.items():
            if cg == gid and t_now - t <= ACTIVE:
                workers[login] = t
        for p in open_prs:
            if t_now - p["updated"] <= ACTIVE:
                workers.setdefault(p["login"], p["created"])
        if g["proved"]:
            state = "proved"
            workers = {}  # nobody is "working" on a gap that is already proved
        elif any(p["verdict"] == "ACCEPTED" for p in open_prs):
            state = "accepted"
        elif any(not p["draft"] and p["verdict"] is None for p in open_prs):
            state = "checking"
        elif workers:
            state = "working"
        else:
            state = "open"
        gap_state[gid] = dict(state=state, title=g["title"], problem=g["problem"], main=g["main"],
                              agents=[dict(login=l, since=t.isoformat()) for l, t in sorted(workers.items(), key=lambda x: x[1])],
                              prs=[dict(number=p["number"], url=p["url"], login=p["login"], verdict=p["verdict"])
                                   for p in open_prs])

    # Active work sessions: one per (account, task). Several agents can share one account.
    def note_sessions(slug=None):
        return {f'{p["login"]} · notes/{p["problem"]} #{p["number"]}' for p in pr_info
                if p["is_note"] and p["state"] == "open" and t_now - p["updated"] <= ACTIVE
                and (slug is None or p["problem"] == slug)}
    active = sorted({f'{a["login"]} · {gid}' for gid, s in gap_state.items() for a in s["agents"]} | note_sessions())
    everyone = sorted({e["login"] for e in events if e.get("login")})
    for e in events:
        e["problem"] = e.get("problem") or (by_id[e["gap"]]["problem"] if e.get("gap") else None)
    events.sort(key=lambda e: e["t"], reverse=True)

    # Per-problem summary: who is working now, what is being checked, activity per day.
    slugs = [x["slug"] for x in yaml.safe_load((ROOT / "site" / "problems.yaml").read_text(encoding="utf-8"))]
    days = [(t_now - dt.timedelta(days=i)).date() for i in range(13, -1, -1)]
    problems = {}
    for slug in slugs:
        gids = [g["id"] for g in gaps if g["problem"] == slug]
        workers = {f'{a["login"]} · {gid}' for gid in gids for a in gap_state[gid]["agents"]}
        workers |= note_sessions(slug)
        per_day = [sum(1 for e in events if e.get("problem") == slug and e["t"].date() == d) for d in days]
        problems[slug] = dict(agents_now=sorted(workers),
                              checking=sum(1 for gid in gids if gap_state[gid]["state"] in ("checking", "accepted")),
                              last=next((e["t"].isoformat() for e in events if e.get("problem") == slug), None),
                              per_day=per_day)
    per_day_all = [sum(1 for e in events if e["t"].date() == d) for d in days]

    # Public leaderboard: proofs merged, proofs accepted by the checker, last activity.
    def board(since_t):
        rows = {}
        for e in events:
            if e["t"] < since_t or not e.get("login"):
                continue
            r = rows.setdefault(e["login"], dict(login=e["login"], proved=0, accepted=0, last=e["t"], last_text=e["text"]))
            if e["kind"] == "merged" and e.get("gap"):
                r["proved"] += 1
            elif e["kind"] == "accepted":
                r["accepted"] += 1
            if e["t"] > r["last"]:
                r["last"], r["last_text"] = e["t"], e["text"]
        out = sorted(rows.values(), key=lambda r: (-r["proved"], -r["accepted"], -r["last"].timestamp()))
        return [{**r, "last": r["last"].isoformat()} for r in out[:10]]
    leaderboard = dict(hour=board(t_now - dt.timedelta(hours=1)), all=board(since))
    highlight = next((e for e in events if e["kind"] in ("merged", "accepted")), None) or (events[0] if events else None)
    return dict(
        generated_at=t_now.isoformat(),
        agents_now=active,
        agents_total=len(everyone),
        gaps=gap_state,
        problems=problems,
        days=[d.isoformat() for d in days],
        per_day=per_day_all,
        last=events[0]["t"].isoformat() if events else None,
        leaderboard=leaderboard,
        just_in={**highlight, "t": highlight["t"].isoformat()} if highlight else None,
        last_hour=sum(1 for e in events if t_now - e["t"] <= dt.timedelta(hours=1)),
        proved=sum(1 for g in gaps if g["proved"]),
        total_gaps=len(gaps),
        events=[{**e, "t": e["t"].isoformat()} for e in events[:80]],
    )


def main() -> int:
    data = collect()
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    print(f"{OUT.relative_to(ROOT)}: {len(data['agents_now'])} agents now, "
          f"{data['agents_total']} so far, {len(data['events'])} events")
    return 0


if __name__ == "__main__":
    sys.exit(main())
