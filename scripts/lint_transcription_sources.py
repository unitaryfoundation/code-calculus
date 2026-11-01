#!/usr/bin/env python3
"""Check 4 of scripts/lint_docs.sh: every transcribed rule has a normative source.

machine/consumer.json and machine/semantics.json are derived transcriptions of
spec/ (AGENTS.md, "Normative artifacts"). Each rule they state carries a
`source` of the form

    spec/<FILE>.md §<section>

where <section> is the leading token of a heading in that file: a section
number such as `2b`, `2d.2`, or `4.25`, or a backticked operation heading
such as `C-SKIP`. The checks are:

  1. every rule in the covered tables carries a `source` string of that form;
  2. the source file exists and lies under spec/;
  3. exactly one heading in that file carries the section token;
  4. for an operation rule, the section's text names the operation, so a rule
     cannot cite a section that does not state it; for a decision rule, the
     section names the decision result;
  5. every rule id is a taxonomy ID defined in spec/TAXONOMY.md, and the ids
     in semantics.json are unique;
  6. every operation with an interval rule in consumer.json has a transition
     rule in semantics.json;
  7. every `.md` path named in any `machine/*.json` resolves (as a
     repo-relative path, or as a bare `spec/` file name, which is how the
     transcriptions cite normative sections) — added 2026-10-29
     after nine references to a since-renamed `an archived note`
     went unnoticed;
  8. `state.json`, `operation_registry.json` and `machine/fixtures/
     mvp_fixtures.json` are covered too: their `source_of_truth` paths
     resolve, the registry ids are taxonomy IDs and unique, and the fixture
     ids are unique `W<n>` records that all carry a boolean
     `acceptance_surface`;
  9. heading uniqueness across `spec/*.md` for **citable** tokens — section
     numbers (`4.25`, `2d.2`, `1a`) and any token that is actually cited as a
     `source` target. A duplicate makes the citation ambiguous, which is the
     defect that forced the 2026-10-29 renumbering of section 4. Generic
     heading words (`Gate`, `Theorem`, `Entry`) are not citable and are not
     held to this rule, since no `source` can point at them.

The covered tables are consumer.json `interval_rules`, `geometry.carry_rules`,
`decision.rules`, and `conditional_inputs`, and semantics.json `rules`. Any
other object carrying a `source` key is checked for resolution (1 to 3) but is
not required to exist.

Run from the repository root. Exit 0 when clean, 1 with findings on stdout.
Standard library only.
"""

import json
import os
import re
import sys

SOURCE_RE = re.compile(r"^(spec/[A-Za-z_]+\.md) §(\S+)$")
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")

findings = []


def finding(msg):
    findings.append(msg)
    print(msg)


def load_json(path):
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def heading_token(text):
    """The leading token of a heading, with markup and trailing punctuation
    stripped: "2b. Consumer interval rules" -> "2b"; "`C-SKIP`" -> "C-SKIP";
    "4.25 — `P-REBASE` ..." -> "4.25"."""
    text = text.replace("`", "").replace("**", "").lstrip("§").strip()
    token = text.split()[0] if text.split() else ""
    return token.rstrip(".:,;—-")


_sections_cache = {}


def sections(path):
    """Map heading token -> list of (level, body) for the file."""
    if path in _sections_cache:
        return _sections_cache[path]
    with open(path, encoding="utf-8") as handle:
        lines = handle.read().split("\n")
    heads = []
    for i, line in enumerate(lines):
        match = HEADING_RE.match(line)
        if match:
            heads.append((i, len(match.group(1)), heading_token(match.group(2))))
    result = {}
    for idx, (start, level, token) in enumerate(heads):
        end = len(lines)
        for later_start, later_level, _ in heads[idx + 1:]:
            if later_level <= level:
                end = later_start
                break
        result.setdefault(token, []).append((level, "\n".join(lines[start:end])))
    _sections_cache[path] = result
    return result


def resolve(source, where):
    """Return the cited section's text, or None after recording a finding."""
    if not isinstance(source, str):
        finding("%s: `source` missing or not a string" % where)
        return None
    match = SOURCE_RE.match(source)
    if not match:
        finding("%s: `source` %r is not of the form `spec/<FILE>.md §<section>`"
                % (where, source))
        return None
    path, token = match.groups()
    if not os.path.isfile(path):
        finding("%s: source file %s does not exist" % (where, path))
        return None
    hits = sections(path).get(token, [])
    if not hits:
        finding("%s: no heading `%s` in %s" % (where, token, path))
        return None
    if len(hits) > 1:
        finding("%s: heading `%s` occurs %d times in %s (ambiguous source)"
                % (where, token, len(hits), path))
        return None
    return hits[0][1]


def names(text, token):
    """Whether the section text names the token as a whole word."""
    return re.search(r"(?<![A-Za-z0-9_-])%s(?![A-Za-z0-9_-])" % re.escape(token),
                     text) is not None


def check_operation_rule(obj, op_id, where):
    if not isinstance(obj, dict):
        finding("%s: rule must be an object carrying `source`" % where)
        return
    text = resolve(obj.get("source"), where)
    if text is not None and not names(text, op_id):
        finding("%s: cited section does not name `%s`" % (where, op_id))


def check_taxonomy(op_id, where, taxonomy_text):
    if not names(taxonomy_text, op_id):
        finding("%s: `%s` is not defined in spec/TAXONOMY.md" % (where, op_id))


def walk_other_sources(obj, path, skip_prefixes):
    """Resolve every `source` outside the covered tables (checks 1 to 3 only)."""
    if any(path == p or path.startswith(p + "/") for p in skip_prefixes):
        return
    if isinstance(obj, dict):
        if "source" in obj and path:
            resolve(obj["source"], path)
        for key, value in obj.items():
            walk_other_sources(value, path + "/" + key, skip_prefixes)
    elif isinstance(obj, list):
        for i, value in enumerate(obj):
            walk_other_sources(value, "%s[%d]" % (path, i), skip_prefixes)


# --- checks added 2026-10-29  -----------------------------

MACHINE_JSON = ["machine/consumer.json", "machine/semantics.json",
                "machine/state.json", "machine/operation_registry.json",
                "machine/fixtures/mvp_fixtures.json"]
MD_TOKEN_RE = re.compile(r'(?<![\w./-])[A-Za-z0-9_][A-Za-z0-9_./-]*\.md(?![\w.])')
SECTION_NUMBER_RE = re.compile(r"^\d+[a-z]?(\.\d+[a-z]?)?$")


def resolves_md(name):
    """A `.md` reference resolves as written, as a bare `spec/` file name (the
    shorthand the transcriptions use when citing a normative section), or — when
    it names no directory — as any file of that basename anywhere in the repo,
    which is how a bare name written before the reorganisation still reads.

    A reference that *does* name a directory must resolve exactly: that is the
    shape a since-moved path has, and it is what nine references to
    `an archived note` looked like before the file's successor was
    found at `an archived note`."""
    if os.path.isfile(name):
        return True
    if os.path.isfile(os.path.join("spec", os.path.basename(name))):
        return True
    if "/" not in name:
        base = os.path.basename(name)
        for root, dirs, names in os.walk("."):
            dirs[:] = [d for d in dirs if d != ".git"]
            if base in names:
                return True
    return False


def check_md_paths():
    """Every `.md` path named in a machine/*.json resolves (check 7)."""
    count = 0
    for path in MACHINE_JSON:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
        for name in sorted(set(MD_TOKEN_RE.findall(text))):
            count += 1
            if not resolves_md(name):
                finding("%s: names %s, which resolves neither as written nor "
                        "under spec/" % (path, name))
    return count


def collected_sources(obj, acc):
    """Every `source` string in a machine/*.json, for citation-target checks."""
    if isinstance(obj, dict):
        for key, value in obj.items():
            if key == "source" and isinstance(value, str):
                acc.append(value)
            collected_sources(value, acc)
    elif isinstance(obj, list):
        for value in obj:
            collected_sources(value, acc)
    return acc


def check_registry(taxonomy_text):
    """operation_registry.json: unique ids, each a taxonomy ID (check 8)."""
    registry = load_json("machine/operation_registry.json")
    seen = set()
    count = 0
    for i, entry in enumerate(registry.get("operations", [])):
        where = "operation_registry.operations[%d]" % i
        if not isinstance(entry, dict) or "id" not in entry:
            finding("%s: entry must carry an `id`" % where)
            continue
        op_id = entry["id"]
        count += 1
        check_taxonomy(op_id, where, taxonomy_text)
        if op_id in seen:
            finding("%s: duplicate operation id %s" % (where, op_id))
        seen.add(op_id)
    return count


def check_fixtures():
    """mvp_fixtures.json: unique `W<n>` ids, each with a boolean
    `acceptance_surface` (check 8). The two sets are named once, in
    spec/OBLIGATIONS.md *Evidence*."""
    fixtures = load_json("machine/fixtures/mvp_fixtures.json")
    records = fixtures.get("fixtures", [])
    if not isinstance(records, list) or not records:
        finding("mvp_fixtures.json: no `fixtures` records found")
        return 0
    seen = set()
    for i, record in enumerate(records):
        where = "mvp_fixtures.fixtures[%d]" % i
        if not isinstance(record, dict):
            finding("%s: record must be an object" % where)
            continue
        rid = record.get("id")
        if not isinstance(rid, str) or not re.match(r"^W\d+$", rid):
            finding("%s: id %r is not a `W<n>` fixture id" % (where, rid))
            continue
        if rid in seen:
            finding("%s: duplicate fixture id %s" % (where, rid))
        seen.add(rid)
        if not isinstance(record.get("acceptance_surface"), bool):
            finding("%s (%s): missing or non-boolean `acceptance_surface`"
                    % (where, rid))
    return len(records)


def check_heading_uniqueness(cited):
    """Heading uniqueness across spec/*.md for citable tokens (check 9).

    A token is citable when it is a section number, or when some machine/*.json
    actually cites it as a `source` target: those are the tokens a rule's
    provenance can name, so a duplicate makes the citation ambiguous. Generic
    heading words (`Gate`, `Theorem`, `Entry`) are not citable and are not held
    to this rule — no `source` can point at them."""
    count = 0
    for path in sorted(p for p in os.listdir("spec") if p.endswith(".md")):
        full = os.path.join("spec", path)
        stem = path[:-3]
        for token, hits in sections(full).items():
            if len(hits) < 2:
                continue
            if SECTION_NUMBER_RE.match(token) or (stem, token) in cited:
                count += 1
                finding("%s: heading token `%s` occurs %d times — ambiguous "
                        "citation target" % (full, token, len(hits)))
    return count


def main():
    with open("spec/TAXONOMY.md", encoding="utf-8") as handle:
        taxonomy_text = handle.read()
    checked = 0

    consumer = load_json("machine/consumer.json")
    covered_consumer = ["interval_rules", "geometry/carry_rules", "decision/rules",
                        "conditional_inputs"]

    interval_rules = consumer.get("interval_rules", {})
    for op_id, rule in interval_rules.items():
        where = "consumer.json interval_rules[%s]" % op_id
        check_taxonomy(op_id, where, taxonomy_text)
        check_operation_rule(rule, op_id, where)
        checked += 1

    for op_id, rule in consumer.get("geometry", {}).get("carry_rules", {}).items():
        where = "consumer.json geometry.carry_rules[%s]" % op_id
        check_taxonomy(op_id, where, taxonomy_text)
        check_operation_rule(rule, op_id, where)
        checked += 1

    for i, rule in enumerate(consumer.get("decision", {}).get("rules", [])):
        where = "consumer.json decision.rules[%d]" % i
        if not isinstance(rule, dict) or "result" not in rule:
            finding("%s: decision rule must be an object with `result`" % where)
            continue
        text = resolve(rule.get("source"), where)
        if text is not None and not names(text, rule["result"]):
            finding("%s: cited section does not name the result `%s`"
                    % (where, rule["result"]))
        checked += 1

    for name, entry in consumer.get("conditional_inputs", {}).items():
        where = "consumer.json conditional_inputs[%s]" % name
        if not isinstance(entry, dict):
            finding("%s: conditional input must be an object carrying `source`" % where)
            continue
        resolve(entry.get("source"), where)
        checked += 1

    walk_other_sources(consumer, "", covered_consumer)

    semantics = load_json("machine/semantics.json")
    seen = {}
    rule_ids = set()
    for i, rule in enumerate(semantics.get("rules", [])):
        where = "semantics.json rules[%d]" % i
        if not isinstance(rule, dict) or "id" not in rule:
            finding("%s: rule must be an object with `id`" % where)
            continue
        op_id = rule["id"]
        where = "semantics.json rules[%d] (%s)" % (i, op_id)
        if op_id in seen:
            finding("%s: duplicate rule id (also rules[%d])" % (where, seen[op_id]))
        seen[op_id] = i
        rule_ids.add(op_id)
        check_taxonomy(op_id, where, taxonomy_text)
        check_operation_rule(rule, op_id, where)
        checked += 1

    walk_other_sources(semantics, "", ["rules"])

    for op_id in interval_rules:
        if op_id not in rule_ids:
            finding("consumer.json interval_rules[%s]: no transition rule with that id "
                    "in semantics.json" % op_id)

    # Checks 7 to 9 : paths in machine/*.json resolve, the three
    # further JSON files are covered, and heading tokens that a rule can cite
    # are unique across spec/.
    checked += check_md_paths()
    checked += check_registry(taxonomy_text)
    checked += check_fixtures()
    cited = set()
    for path in MACHINE_JSON:
        for source in collected_sources(load_json(path), []):
            match = SOURCE_RE.match(source)
            if match:
                cited.add((os.path.basename(match.group(1))[:-3], match.group(2)))
    checked += check_heading_uniqueness(cited)

    if findings:
        print("transcription sources FAILED: %d finding(s), %d rules checked"
              % (len(findings), checked))
        return 1
    print("transcription sources ok: %d rules checked" % checked)
    return 0


if __name__ == "__main__":
    sys.exit(main())
