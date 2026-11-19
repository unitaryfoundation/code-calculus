#!/usr/bin/env python3
"""Report the correspondence between the private dev repo and the public repo.

This is a maintainer tool. It does not modify either tree. It walks the public
tree, pairs each file with the file at the same relative path in the dev tree,
and reports:

  * identical          - byte-identical copies
  * sanitized-differs  - same path, different bytes (expected to be the
                        documented redaction of internal references)
  * public-only        - present in the public tree but not in the dev tree
  * dev-only (top-level)- top-level entries present in dev but not in public

Generated/cache artifacts are skipped by default. Pass --include-generated to
keep them in the report.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path


SKIP_DIR_NAMES = {".git", "__pycache__", ".pytest_cache"}
SKIP_SUFFIXES = (".pyc",)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def is_generated(rel: Path) -> bool:
    parts = rel.parts
    if any(part in SKIP_DIR_NAMES for part in parts):
        return True
    if rel.suffix in SKIP_SUFFIXES:
        return True
    # Common generated reports in the consumer tree.
    if rel.name.endswith("_report.json"):
        return True
    return False


def walk_files(root: Path, include_generated: bool):
    result = []
    for dirpath, dirnames, filenames in os.walk(root):
        # prune skipped dirs in place
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIR_NAMES]
        for fn in filenames:
            p = Path(dirpath) / fn
            rel = p.relative_to(root)
            if (not include_generated) and is_generated(rel):
                continue
            result.append(rel)
    return sorted(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dev", required=True, help="path to code-calculus-dev checkout")
    parser.add_argument("--public", required=True, help="path to code-calculus checkout")
    parser.add_argument("--json", dest="json_out", default=None, help="write machine-readable report to this path")
    parser.add_argument("--include-generated", action="store_true", help="include cache/report artifacts")
    args = parser.parse_args()

    dev_root = Path(args.dev).resolve()
    pub_root = Path(args.public).resolve()

    pub_files = walk_files(pub_root, args.include_generated)

    identical = []
    differs = []
    public_only = []

    for rel in pub_files:
        dev_path = dev_root / rel
        pub_path = pub_root / rel
        if not dev_path.is_file():
            public_only.append(str(rel))
            continue
        if sha256(dev_path) == sha256(pub_path):
            identical.append(str(rel))
        else:
            differs.append(str(rel))

    dev_top = sorted(p.name for p in dev_root.iterdir() if p.exists())
    pub_top = sorted(p.name for p in pub_root.iterdir() if p.exists())
    dev_only_top = sorted(set(dev_top) - set(pub_top))

    report = {
        "dev_root": str(dev_root),
        "public_root": str(pub_root),
        "counts": {
            "public_files_considered": len(pub_files),
            "identical": len(identical),
            "sanitized_differs": len(differs),
            "public_only": len(public_only),
            "dev_only_top_level": len(dev_only_top),
        },
        "identical": identical,
        "sanitized_differs": differs,
        "public_only": public_only,
        "dev_only_top_level": dev_only_top,
    }

    if args.json_out:
        Path(args.json_out).write_text(json.dumps(report, indent=2) + "\n")

    print("Public/dev correspondence report")
    print("  dev:     %s" % dev_root)
    print("  public:  %s" % pub_root)
    print("  files considered: %d" % len(pub_files))
    print("  identical:        %d" % len(identical))
    print("  sanitized-differs:%d" % len(differs))
    print("  public-only:      %d" % len(public_only))
    print("  dev-only (top):   %d" % len(dev_only_top))
    print()
    if differs:
        print("Sanitized-differs (%d):" % len(differs))
        for r in differs:
            print("  D  " + r)
        print()
    if public_only:
        print("Public-only (%d):" % len(public_only))
        for r in public_only:
            print("  P  " + r)
        print()
    if dev_only_top:
        print("Dev-only top-level entries (%d):" % len(dev_only_top))
        for r in dev_only_top:
            print("  V  " + r)
        print()
    print("Note: 'sanitized-differs' is expected for files whose public copy has")
    print("internal issue numbers, red-team finding IDs, or private note names")
    print("redacted. Inspect any unexpected entry manually.")


if __name__ == "__main__":
    main()