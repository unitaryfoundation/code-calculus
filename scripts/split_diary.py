#!/usr/bin/env python3
"""Split the monolithic DIARY.md into per-entry fragments under diary/."""
import re
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIARY = ROOT / "DIARY.md"
DIARY_DIR = ROOT / "diary"

text = DIARY.read_text()

# Find all entry header positions.
pattern = re.compile(r"(?m)^## \d{4}-\d{2}-\d{2}.*$")
matches = list(pattern.finditer(text))
assert matches, "no entries found"

# Header: everything before the first entry.
header = text[:matches[0].start()].rstrip() + "\n"

DIARY_DIR.mkdir(exist_ok=True)
for f in DIARY_DIR.glob("*.md"):
    f.unlink()

index_lines = [header.rstrip(), "", "## Entries (newest first)", "",
               "Each entry lives in its own file under [`diary/`](diary/) so concurrent",
               "PRs never contend on a single file. Append a new fragment; do not edit",
               "an old one (supersede it with a new dated entry instead).", ""]

seen = set()
count = 0
for i, m in enumerate(matches):
    start = m.start()
    end = matches[i+1].start() if i+1 < len(matches) else len(text)
    entry = text[start:end]
    # drop separator lines that sit between entries
    entry = '\n'.join(l for l in entry.splitlines() if l.strip() != '---').rstrip() + '\n'
    first_line = entry.splitlines()[0]
    t = first_line[2:].strip()  # drop '## '
    date = t[:10]
    rest = t[10:].lstrip(": ").strip()
    s = re.sub(r"[^A-Za-z0-9]+", "-", rest).strip("-").lower()
    if len(s) > 60:
        s = s[:60].rstrip("-")
    base = f"{date}-{s}" if s else date
    fname = base + ".md"
    path = DIARY_DIR / fname
    j = 2
    while path.exists() or path.name in seen:
        path = DIARY_DIR / f"{base}-{j}.md"
        j += 1
    seen.add(path.name)
    path.write_text(entry)
    count += 1
    index_lines.append(f"- [{t}](diary/{path.name})")

(DIARY_DIR / "README.md").write_text(
    "# Diary fragments\n\n"
    "One file per dated decision. Newest first by filename (ISO date prefix).\n"
    "Do not edit an old fragment; supersede it with a new dated entry.\n"
    "See the parent `DIARY.md` for the rule and index.\n"
)

DIARY.write_text("\n".join(index_lines) + "\n")
print(f"split {count} entries into {DIARY_DIR}")
