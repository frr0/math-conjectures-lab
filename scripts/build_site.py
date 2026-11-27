#!/usr/bin/env python3
"""Build the static GitHub Pages site into _site/.

The site is data-driven: this script extracts the catalogue table from README.md and
every results/<slug>/README.md into _site/data.json, and copies site/ (index.html,
style.css, app.js), which renders the data client-side (marked + KaTeX).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "_site"
REPO = os.environ.get("GITHUB_REPOSITORY", "frr0/math-conjectures-lab")

ROW = re.compile(
    r"^\|\s*(\d+)\s*\|(.+?)\|(.+?)\|\s*(\S+)\s*\|\s*\[([\w-]+)\]\(results/[\w-]+/?\)\s*\|\s*$"
)


def git(*args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def lean_module(slug: str) -> str | None:
    # oeis-a001227 -> OeisA001227
    name = "".join(part[:1].upper() + part[1:] for part in slug.split("-"))
    path = ROOT / "lean" / "ConjectureLab" / f"{name}.lean"
    return f"lean/ConjectureLab/{name}.lean" if path.exists() else None


def main() -> int:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    entries = []
    for line in readme.splitlines():
        m = ROW.match(line)
        if not m:
            continue
        num, title, outcome, badge, slug = (g.strip() for g in m.groups())
        res = ROOT / "results" / slug / "README.md"
        if not res.exists():
            raise SystemExit(f"catalogue row {num} points to missing {res}")
        files = sorted(p.name for p in (ROOT / "results" / slug).iterdir() if p.is_file())
        entries.append(
            {
                "num": int(num),
                "slug": slug,
                "title": title,
                "outcome": outcome,
                "badge": badge,
                "readme": res.read_text(encoding="utf-8"),
                "files": files,
                "lean": lean_module(slug),
                "updated": git("log", "-1", "--format=%cs", "--", f"results/{slug}"),
            }
        )
    if not entries:
        raise SystemExit("no catalogue rows parsed from README.md")

    data = {
        "repo": REPO,
        "commit": os.environ.get("GITHUB_SHA") or git("rev-parse", "HEAD"),
        "commit_date": git("log", "-1", "--format=%cI"),
        "commit_subject": git("log", "-1", "--format=%s"),
        "entries": entries,
    }
    if OUT.exists():
        shutil.rmtree(OUT)
    shutil.copytree(ROOT / "site", OUT)
    (OUT / "data.json").write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
    (OUT / ".nojekyll").write_text("", encoding="utf-8")
    print(f"built {OUT.relative_to(ROOT)} with {len(entries)} entries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
