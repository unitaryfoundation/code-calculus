#!/bin/sh
# End-to-end check of the formal-certificate pipeline (issues #645, #647) on
# the board entry codes/10-2-3-b.json of a qldpc-challenge checkout.
#
# Usage: sh scripts/check_formal_cert_pipeline.sh QLDPC_CHALLENGE_DIR
#
# 1. machine/experiments/formal_cert_from_challenge.py generates the module,
#    builds it with lake, and checks the axioms of <name>_certified.
# 2. The module is put in a commit object that no branch points at, so the
#    payload's commit holds the theorem, as it must for a real submission.
# 3. The payload printed for that commit goes through the board's own
#    verify/check_certs.py in a temporary tree.
#
# Needs lake (with the default target built), Python >= 3.10, and the
# checker's numpy and jsonschema. Leaves no file and moves no branch.
set -eu

QLDPC=$(cd "${1:?usage: $0 QLDPC_CHALLENGE_DIR}" && pwd)
cd "$(dirname "$0")/.."

SLUG=10-2-3-b
NAME=qldpc_10_2_3_b
ENTRY=$QLDPC/codes/$SLUG.json
GEN=machine/experiments/formal_cert_from_challenge.py
MODULE=lean/CodeCalculus/FormalCerts/$NAME.lean
PYTHON=${PYTHON:-python3}

if [ -e "$MODULE" ]; then
  echo "$MODULE exists; not overwriting it" >&2
  exit 1
fi
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"; rm -f "$MODULE"; rmdir lean/CodeCalculus/FormalCerts 2>/dev/null || true' EXIT

echo "== generate, build, and check axioms"
"$PYTHON" "$GEN" "$ENTRY" --name "$NAME"

echo "== pin the module in a commit object"
cp "$(git rev-parse --git-dir)/index" "$SCRATCH/index"
export GIT_AUTHOR_NAME=formal-cert-check GIT_AUTHOR_EMAIL=check@example.invalid
export GIT_COMMITTER_NAME=formal-cert-check GIT_COMMITTER_EMAIL=check@example.invalid
GIT_INDEX_FILE=$SCRATCH/index git add -f "$MODULE"
TREE=$(GIT_INDEX_FILE=$SCRATCH/index git write-tree)
COMMIT=$(git commit-tree "$TREE" -p HEAD -m "formal-certificate pipeline check")

echo "== payload for $COMMIT"
"$PYTHON" "$GEN" "$ENTRY" --name "$NAME" --repo github.com/example/check \
  --commit "$COMMIT" > "$SCRATCH/payload.json"
cat "$SCRATCH/payload.json"

echo "== verify/check_certs.py in a temporary tree"
TREE_DIR=$SCRATCH/board
mkdir -p "$TREE_DIR/codes" "$TREE_DIR/certs"
cp -R "$QLDPC/verify" "$QLDPC/schema" "$TREE_DIR/"
cp "$ENTRY" "$TREE_DIR/codes/$SLUG.json"
cp "$SCRATCH/payload.json" "$TREE_DIR/certs/$SLUG.json"
if ! OUT=$(cd "$TREE_DIR" && "$PYTHON" verify/check_certs.py 2>&1); then
  echo "$OUT"
  echo "check_certs.py rejected the payload" >&2
  exit 1
fi
echo "$OUT"
case $OUT in
  *"jsonschema unavailable"*)
    echo "jsonschema is not installed; the schema check did not run" >&2
    exit 1 ;;
esac
case $OUT in
  *"ok: 1 certificates valid"*"1 formal"*) ;;
  *) echo "check_certs.py did not accept the payload as formal" >&2; exit 1 ;;
esac
