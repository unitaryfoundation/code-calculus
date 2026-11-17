#!/bin/sh
# Documentation-consistency lint for the code-calculus planning repository.
#
# Checks:
#   1. every relative markdown link target resolves to a file in this repo;
#   2. every taxonomy ID token (e.g. C-DELETE-CHECK) is defined in spec/TAXONOMY.md;
#   3. every OBL-* obligation name is defined in spec/OBLIGATIONS.md;
#   4. every rule transcribed in machine/consumer.json and machine/semantics.json
#      carries a `source` that resolves to one spec/ section naming the
#      operation (scripts/lint_transcription_sources.py);
#   5. malformed links are reported: a backtick-quoted path used as a link
#      without brackets (`X.md`(Y)), doubled opening brackets before a link,
#      and link *text* that names a file which exists nowhere in the repo.
#
# ID tokens are extracted as maximal runs of uppercase letters, digits, and
# hyphens, so substrings like "OBL-SKIP-IDENTITY" or "QLDPC-LAYA" do not leak
# look-alike IDs ("L-SKIP-IDENTITY", "C-LAYA"). Checks 2 and 3 match a whole
# word, so an ID is never satisfied by a longer token that merely contains it
# (hardened 2026-10-29; RG-21).
#
# Usage: sh scripts/lint_docs.sh   (exit 0 = clean, 1 = findings)

set -u
cd "$(dirname "$0")/.." || exit 2

fail=0
files=$(find . \( -path './.git' -o -path './.venv' -o -path './lean/.lake' \) -prune -o -name '*.md' -print | sort)

# 1. Relative markdown link targets resolve.
for f in $files; do
  dir=$(dirname "$f")
  targets=$(grep -oE '\]\([^)]*\)' "$f" | sed -e 's/^](//' -e 's/)$//' \
    | grep -vE '^(https?://|mailto:|#)' | sed -e 's/#.*//' -e '/^$/d' | sort -u)
  for t in $targets; do
    if [ ! -e "$dir/$t" ]; then
      echo "broken link: $f -> $t"
      fail=1
    fi
  done
done

# 2. Taxonomy IDs (tokens starting with P-/C-/E-/A-/L-/X-) are defined in
#    spec/TAXONOMY.md. `grep -w` is used, which treats a hyphen as a word
#    boundary, so a token is also matched inside a longer hyphenated token
#    (e.g. E-GRAFT inside E-GRAFT-FOO); the token extraction above already
#    stops the substring leak for taxonomy IDs, but the check is not a true
#    whole-word test. Tokens ending in a hyphen are line fragments rather than
#    IDs, so they are dropped.
for id in $(grep -hoE '[A-Z][A-Z0-9-]*' $files | grep -E '^[PECALX]-' | grep -vE -- '-$' | sort -u); do
  if ! grep -qw "$id" spec/TAXONOMY.md; then
    echo "undefined taxonomy ID: $id"
    fail=1
  fi
done

# 3. Obligation names are defined in spec/OBLIGATIONS.md.
for id in $(grep -hoE 'OBL-[A-Z][A-Z0-9-]*' $files | grep -vE -- '-$' | sort -u); do
  if ! grep -qw "$id" spec/OBLIGATIONS.md; then
    echo "undefined obligation name: $id"
    fail=1
  fi
done

# 4. Transcribed rules carry a resolving normative source.
if ! python3 scripts/lint_transcription_sources.py; then
  fail=1
fi

# 5. Malformed links, in the live tree only. (a) a backtick-quoted path used as
#    a link without brackets -- `spec/X.md`(spec/X.md) renders as code plus
#    parentheses, so the reference never becomes clickable; (b) a doubled
#    opening bracket, the signature of a relabel substitution that ate one
#    bracket; (c) link *text* that names a file which exists nowhere in the
#    repository, while the target points at its successor.
#
live=$(echo "$files")
for f in $live; do
  if grep -nE '`[^`]*\.(md|json|py|lean)`\([^)]*\)' "$f" >/dev/null; then
    grep -nE '`[^`]*\.(md|json|py|lean)`\([^)]*\)' "$f" | sed "s|^|$f: |"
    echo "^ pseudo-link: a backtick-quoted path used as a link, without brackets"
    fail=1
  fi
  if grep -nE '\[\[[^]]*\]\(' "$f" >/dev/null; then
    grep -nE '\[\[[^]]*\]\(' "$f" | sed "s|^|$f: |"
    echo "^ doubled opening bracket before a link"
    fail=1
  fi
done

# 5c. Link text that names a file which exists nowhere in the repository.
#     The target may legitimately differ from the text (an archived file at its
#     new path), so the text is allowed to name any file anywhere in the repo.
badtext=$(grep -ohE '\[`[^]]*`[^]]*\]\([^)]*\)' $live \
  | grep -oE '`[^`]+`' | tr -d '`' \
  | grep -E '\.(md|json|py|lean)$' | sort -u | while read -r name; do
      base=$(basename "$name")
      if [ -z "$(find . \( -path './.git' -o -path './.venv' -o -path './lean/.lake' \) -prune -o -name "$base" -print -quit)" ]; then
        echo "$name"
      fi
    done)
if [ -n "$badtext" ]; then
  echo "$badtext" | sed 's|^|link text names a file that exists nowhere: |'
  fail=1
fi

# 6. No unresolved merge-conflict markers anywhere in the tracked tree.
cm=$(grep -rlE '^(<<<<<<<|=======$|>>>>>>>)' . --exclude-dir=.git --exclude-dir=.venv --exclude-dir=.lake   --include='*.md' --include='*.py' --include='*.lean' --include='*.json'   --include='*.yml' --include='*.yaml' --include='*.sh' --include='*.txt' 2>/dev/null   | grep -v '^./.git/' | grep -v '^./.venv/' | grep -v '^./lean/.lake/' | grep -v '^./machine/requirements' || true)
if [ -n "$cm" ]; then
  echo "unresolved conflict markers found:"
  for f in $cm; do
    grep -nE '^(<<<<<<<|=======$|>>>>>>>)' "$f" | sed "s|^|$f: |"
  done
  fail=1
fi

# 7. The accepted axiom set in lean/extra/ClosedK.lean is frozen: exactly the
#    four rank axioms listed in AXIOMS.md. Any change requires updating both.
axioms_found=$(grep -oE '^axiom [A-Za-z_]+' lean/extra/ClosedK.lean | sort)
axioms_expected=$(printf '%s\n' 'axiom hgp_rankX' 'axiom hgp_rankZ' 'axiom product_rankX' 'axiom product_rankZ' | sort)
if [ "$axioms_found" != "$axioms_expected" ]; then
  echo "axiom set in lean/extra/ClosedK.lean changed:"
  echo "--- found ---"; echo "$axioms_found"
  echo "--- expected ---"; echo "$axioms_expected"
  echo "Update AXIOMS.md and this check together."
  fail=1
fi

n=$(echo "$files" | wc -l | tr -d ' ')
if [ "$fail" -eq 0 ]; then
  echo "lint ok: $n markdown files checked"
else
  echo "lint FAILED: findings above ($n markdown files checked)"
fi
exit "$fail"
