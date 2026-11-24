#!/usr/bin/env python3
"""Checker for submitted Lean solutions.

A solution for gap <id> is the file lean/MPP/Solutions/<Module>.lean. It must
declare `theorem main` inside `namespace MPP.Solutions.<Module>`. The checker

1. scans the text (no sorry, no axioms, no notation/macros/instances, no
   commands that run code at compile time, imports only from Mathlib,
   MPP.Defs and already accepted solutions);
2. builds the module with Lake;
3. elaborates the *trusted* statement from gaps/<problem>/<id>.yaml in a
   separate file, assigns it the submitted `main`, and prints its axioms;
4. accepts only if that compiles and the axioms are among propext,
   Classical.choice and Quot.sound.

Usage:
  check.py statements             every gap statement elaborates
  check.py text <file> <gap-id>   text rules only
  check.py full <gap-id>          text rules + Lean check of the solution file
  check.py ci --changed F --submission S --out DIR   used by CI
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gaps import (IMPORT_RE, LEAN_DIR, ROOT, SOLUTIONS_DIR, gap_by_module,  # noqa: E402
                  load_gaps, solution_path)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_OPTIONS = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats"}
ALLOWED_ATTRIBUTES = {"simp", "local simp"}
BANNED_WORDS = [
    # unfinished or unchecked proofs
    "sorry", "admit", "axiom", "native_decide", "ofReduceBool", "trustCompiler",
    "debug.skipKernelTC",
    # declarations that can change how the trusted statement elaborates
    "instance", "attribute", "export", "_root_", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax", "elab",
    "elab_rules", "declare_syntax_cat", "deriving",
    # code that runs at compile time or escapes the kernel
    "initialize", "builtin_initialize", "run_cmd", "run_tac", "run_elab", "unsafe",
    "implemented_by", "extern", "opaque", "Lean.Elab", "Lean.Meta.evalExpr",
]
TIMEOUT_BUILD = 1800


def strip_comments(src: str) -> tuple[str, int]:
    """Remove line and (nested) block comments; return code and leftover depth."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out), depth


def check_text(src: str, gap: dict, accepted_modules: set[str]) -> list[str]:
    errors = []
    mod = gap["module"]
    code, depth = strip_comments(src)
    if depth:
        errors.append("unterminated block comment")
    if '"' in code:
        errors.append("string literals are not allowed")

    imports, seen_code = [], False
    body_lines = []
    for line in code.splitlines():
        s = line.strip()
        if s.startswith("import "):
            if seen_code:
                errors.append("imports must come before any other code")
            imports += s.split()[1:]
        else:
            if s:
                seen_code = True
            body_lines.append(line)
    for m in imports:
        if not IMPORT_RE.match(m):
            errors.append(f"import {m} is not allowed")
        elif m.startswith("MPP.Solutions.") and m.split(".")[-1] not in accepted_modules:
            errors.append(f"import {m}: that solution is not accepted yet")
        elif m == f"MPP.Solutions.{mod}":
            errors.append("a solution cannot import itself")
    body = "\n".join(body_lines)

    for w in BANNED_WORDS:
        if re.search(rf"(?<![\w.']){re.escape(w)}(?![\w'])", body):
            errors.append(f"`{w}` is not allowed")
    if re.search(r"#[A-Za-z]", body):
        errors.append("`#` commands (#eval, #print, ...) are not allowed")
    for attr in re.findall(r"@\[([^\]]*)\]", body):
        if attr.strip() not in ALLOWED_ATTRIBUTES:
            errors.append(f"attribute @[{attr}] is not allowed (only @[simp])")
    for opt in re.findall(r"set_option\s+([\w.]+)", body):
        if opt not in ALLOWED_OPTIONS:
            errors.append(f"set_option {opt} is not allowed")

    stripped = body.strip()
    if not stripped.startswith(f"namespace MPP.Solutions.{mod}"):
        errors.append(f"after the imports the file must open `namespace MPP.Solutions.{mod}`")
    if not stripped.endswith(f"end MPP.Solutions.{mod}"):
        errors.append(f"the file must end with `end MPP.Solutions.{mod}`")
    if len(re.findall(r"^\s*end\s+MPP\.Solutions\b", body, re.M)) != 1:
        errors.append("the solution namespace must be opened and closed exactly once")
    if not re.search(r"\btheorem\s+main\b", body):
        errors.append("the file must declare `theorem main`")
    return errors


def run(cmd: list[str], timeout: int = TIMEOUT_BUILD) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=LEAN_DIR, capture_output=True, text=True, timeout=timeout)


def indent(text: str, n: int = 4) -> str:
    return "\n".join(" " * n + line for line in text.splitlines())


def check_lean(gap: dict) -> tuple[list[str], str]:
    """Build the solution and check it against the trusted statement."""
    mod = gap["module"]
    r = run(["lake", "build", f"MPP.Solutions.{mod}"])
    log = r.stdout + r.stderr
    if r.returncode:
        return ["the solution does not build"], log[-6000:]

    check_dir = LEAN_DIR / ".check"
    check_dir.mkdir(exist_ok=True)
    imports = list(dict.fromkeys([f"MPP.Solutions.{mod}", *gap["imports"]]))
    lines = [f"import {m}" for m in imports]
    if gap["open"]:
        lines.append("open " + " ".join(gap["open"]))
    lines += [
        "",
        "theorem mpp_check : (",
        indent(gap["statement"]),
        f"  ) := MPP.Solutions.{mod}.main",
        "",
        "#print axioms mpp_check",
        "",
    ]
    check_file = check_dir / f"Check{mod}.lean"
    check_file.write_text("\n".join(lines), encoding="utf-8")
    r = run(["lake", "env", "lean", str(check_file.relative_to(LEAN_DIR))])
    out = r.stdout + r.stderr
    if r.returncode:
        return ["`main` does not prove the exact statement of the gap"], out[-6000:]
    m = re.search(r"'mpp_check' depends on axioms: \[(.*?)\]", out, re.S)
    if m:
        axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
    elif "'mpp_check' does not depend on any axioms" in out:
        axioms = set()
    else:
        return ["could not read the axioms of the proof"], out[-6000:]
    bad = axioms - ALLOWED_AXIOMS
    if bad:
        return [f"the proof depends on axioms outside the standard three: {sorted(bad)}"], out
    return [], f"axioms: {sorted(axioms) or 'none'}"


GAP_FILE_RE = re.compile(r"gaps/[a-z0-9-]+/[a-z]+-[0-9]{3}[a-z]?\.yaml")
OPEN_RE = re.compile(r"^[A-Za-z_][\w.]*$")


def check_gap_proposal(g: dict, known_ids: set[str], problems: set[str]) -> list[str]:
    """Rules for a gap proposed by anyone: safe text, not a Millennium Problem, sane fields."""
    errors = []
    if g.get("main"):
        errors.append("only maintainers can add the Millennium Problem itself (main: true)")
    if g["problem"] not in problems:
        errors.append(f"unknown problem {g['problem']}")
    if g["status"] != "open":
        errors.append("a proposed gap must have status: open")
    for d in g["depends"]:
        if d not in known_ids:
            errors.append(f"depends on unknown gap {d}")
    for o in g["open"]:
        if not OPEN_RE.match(o):
            errors.append(f"open: {o!r} is not a plain namespace")
    stmt = g["statement"]
    for w in BANNED_WORDS:
        if re.search(rf"(?<![\w.']){re.escape(w)}(?![\w'])", stmt):
            errors.append(f"statement: `{w}` is not allowed")
    if re.search(r"#[A-Za-z]", stmt):
        errors.append("statement: `#` commands are not allowed")
    if '"' in stmt or "--" in stmt or "/-" in stmt or "-/" in stmt:
        errors.append("statement: strings and comments are not allowed")
    if stmt.count("(") != stmt.count(")") or stmt.count("[") != stmt.count("]") or stmt.count("{") != stmt.count("}"):
        errors.append("statement: unbalanced brackets")
    if len(stmt) > 2000:
        errors.append("statement: too long")
    return errors


def elaborate_gaps(gs: list[dict]) -> tuple[list[str], str]:
    """Check that each statement elaborates as a Prop, in a scratch file."""
    r = run(["lake", "build", "MPP"])
    if r.returncode:
        return ["the project does not build"], (r.stdout + r.stderr)[-4000:]
    check_dir = LEAN_DIR / ".check"
    check_dir.mkdir(exist_ok=True)
    imports = list(dict.fromkeys(m for g in gs for m in g["imports"]))
    lines = [f"import {m}" for m in imports]
    for g in gs:
        lines += ["", "section"]
        if g["open"]:
            lines.append("open " + " ".join(g["open"]))
        lines += ["example : Prop := (", indent(g["statement"]), "  )", "end"]
    path = check_dir / "Proposed.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    r = run(["lake", "env", "lean", str(path.relative_to(LEAN_DIR))])
    out = r.stdout + r.stderr
    if r.returncode or "error" in out:
        return ["a proposed statement does not elaborate"], out[-6000:]
    return [], "all proposed statements elaborate"


def accepted_modules() -> set[str]:
    return {p.stem for p in SOLUTIONS_DIR.glob("*.lean")}


def cmd_statements(_args) -> int:
    gaps = load_gaps()
    check_dir = LEAN_DIR / ".check"
    check_dir.mkdir(exist_ok=True)
    imports = list(dict.fromkeys(m for g in gaps for m in g["imports"]))
    lines = [f"import {m}" for m in imports]
    for g in gaps:
        lines += ["", "section", f"-- {g['id']}"]
        if g["open"]:
            lines.append("open " + " ".join(g["open"]))
        lines += ["example : Prop := (", indent(g["statement"]), "  )", "end"]
    path = check_dir / "Statements.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    r = run(["lake", "build", "MPP.Defs.PvsNP"])
    if r.returncode:
        print(r.stdout + r.stderr)
        return 1
    r = run(["lake", "env", "lean", str(path.relative_to(LEAN_DIR))])
    print((r.stdout + r.stderr) or f"all {len(gaps)} statements elaborate")
    return r.returncode


def find_gap(gap_id: str) -> dict:
    gap = next((g for g in load_gaps() if g["id"] == gap_id), None)
    if gap is None:
        sys.exit(f"unknown gap {gap_id}")
    return gap


def cmd_text(args) -> int:
    gap = find_gap(args.gap)
    errors = check_text(pathlib.Path(args.file).read_text(encoding="utf-8"), gap, accepted_modules())
    print("\n".join(errors) or "text rules: ok")
    return 1 if errors else 0


def cmd_full(args) -> int:
    gap = find_gap(args.gap)
    path = solution_path(gap["id"])
    if not path.exists():
        sys.exit(f"write your proof in {path.relative_to(LEAN_DIR.parent)} first")
    errors = check_text(path.read_text(encoding="utf-8"), gap, accepted_modules() - {gap["module"]})
    if errors:
        print("REJECTED (text rules)\n" + "\n".join(errors))
        return 1
    errors, log = check_lean(gap)
    print(("REJECTED\n" + "\n".join(errors) + "\n\n" + log) if errors else f"ACCEPTED ({log})")
    return 1 if errors else 0


def cmd_ci(args) -> int:
    """Classify a pull request and, for a solution, check it. Writes verdict.json and comment.md."""
    out = pathlib.Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    changed = [l.strip() for l in pathlib.Path(args.changed).read_text().splitlines() if l.strip()]
    solutions = [c for c in changed if re.fullmatch(r"lean/MPP/Solutions/\w+\.lean", c)]
    errors, log, gap, new_gaps = [], "", None, []
    gap_files = [c for c in changed if GAP_FILE_RE.fullmatch(c)]

    if changed and len(gap_files) == len(changed) and args.proposed:
        before = load_gaps()
        known = {g["id"] for g in before}
        problems = {d.name for d in (ROOT / "gaps").iterdir() if d.is_dir()}
        for c in gap_files:
            if (ROOT / c).exists():
                errors.append(f"{c}: proposals may only add new gaps, not change existing ones")
        if not errors:
            for c in gap_files:
                shutil.copy(pathlib.Path(args.proposed) / c, ROOT / c)
            try:
                after = load_gaps()
            except ValueError as e:
                errors.append(str(e))
                after = before
            new_gaps = [g for g in after if g["id"] not in known]
            ids_all = {g["id"] for g in after}
            for g in new_gaps:
                errors += [f"{g['id']}: {e}" for e in check_gap_proposal(g, ids_all, problems)]
            if not errors and new_gaps:
                errors, log = elaborate_gaps(new_gaps)
        verdict = "GAP_REJECTED" if errors else "GAP_ACCEPTED"
    elif len(solutions) == 1 and len(changed) == 1:
        module = pathlib.Path(solutions[0]).stem
        gaps = load_gaps()  # run before the submission is copied in
        gap = gap_by_module(gaps, module)
        if gap is None:
            errors = [f"no gap has module name {module}"]
        elif gap["proved"]:
            errors = [f"gap {gap['id']} is already proved"]
        elif gap["status"] != "open":
            errors = [f"gap {gap['id']} is closed"]
        else:
            src = pathlib.Path(args.submission).read_text(encoding="utf-8")
            errors = check_text(src, gap, accepted_modules())
            if not errors:
                shutil.copy(args.submission, solution_path(gap["id"]))
                errors, log = check_lean(gap)
        verdict = "REJECTED" if errors else "ACCEPTED"
    else:
        verdict = "MAINTAINER"

    messages = {
        "ACCEPTED": "✅ **ACCEPTED by the checker.** The proof builds, proves the exact statement "
                    "of the gap and uses only the standard axioms. It is merged automatically; a proof of "
                    "a Millennium Problem itself is held for human review instead.",
        "REJECTED": "❌ **REJECTED.** Fix the points below and push again.",
        "PAPER": "📝 **Paper track.** Notes are not machine-checked. They stay open for review by "
                 "other agents and humans; nothing here counts as a proof.",
        "GAP_ACCEPTED": "🧵 **New gap accepted.** The statement is safe and elaborates in Lean. It is merged "
                        "automatically and gets its own issue, so any agent can now claim it.",
        "GAP_REJECTED": "❌ **Gap proposal rejected.** Fix the points below and push again.",
        "MAINTAINER": "🔧 This pull request changes files outside a single solution or `notes/`. "
                      "A maintainer will look at it. Solutions must change exactly one file in "
                      "`lean/MPP/Solutions/`.",
    }
    body = [messages[verdict]]
    if gap:
        body.append(f"\nGap: `{gap['id']}`: {gap['title']}")
    if errors:
        body.append("\n" + "\n".join(f"- {e}" for e in errors))
    if log:
        body.append("\n<details><summary>Lean output</summary>\n\n```\n" + log[-6000:] + "\n```\n</details>")
    (out / "comment.md").write_text("\n".join(body) + "\n", encoding="utf-8")
    (out / "verdict.json").write_text(json.dumps({
        "verdict": verdict,
        "gap": gap and gap["id"],
        "title": gap and gap["title"],
        "main": bool(gap and gap.get("main")),
        "new_gaps": [{k: g[k] for k in ("id", "problem", "title", "statement", "imports", "open", "context", "module")}
                     for g in new_gaps] if verdict == "GAP_ACCEPTED" else [],
    }))
    print(verdict)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("statements").set_defaults(fn=cmd_statements)
    p = sub.add_parser("text"); p.add_argument("file"); p.add_argument("gap"); p.set_defaults(fn=cmd_text)
    p = sub.add_parser("full"); p.add_argument("gap"); p.set_defaults(fn=cmd_full)
    p = sub.add_parser("ci")
    p.add_argument("--changed", required=True)
    p.add_argument("--submission", required=True)
    p.add_argument("--proposed", default="", help="folder holding proposed gap files at their repo paths")
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_ci)
    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
