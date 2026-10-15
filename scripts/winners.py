#!/usr/bin/env python3
"""List the confirmed faster_step edits of a lint_afp.py run, and linter_retime inputs for them.

Usage: scripts/winners.py RUN OUT.tsv [RETIME.tsv [RETIME_PATCHED.tsv]]
RUN is a lint_afp.py output dir (census/pc/faster_step): entry copies and logs/SESSION.tsv.
OUT has one row per winner with its place in the AFP original and in the patched copy.
RETIME files are census-style rows (`linter_retime -I`) for the original steps in the AFP and
for the new steps in the patched copies, at the paths they have on the timing PC.
"""

import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from edit_summary import SPEEDUP, kind, props
from lint_afp import AFP, SESSION, SUFFIX

PC_AFP = "~/dev/etc/afp/afp-2026-10-01/thys"
PC_RUN = "~/dev/isabelle_linter/census/faster_step"
SYMBOL = re.compile(r"\\<\^?[A-Za-z][A-Za-z0-9_']*>|\r\n|.", re.S)


def read_text(path):
    with open(path, newline="") as f:
        return f.read()


# Isabelle symbol offset (from 1) of a text offset (from 0), as build timings store it
def symbol_offset(text, offset):
    return len(SYMBOL.findall(text[:offset])) + 1


def line_of(text, offset):
    return text.count("\n", 0, offset) + 1


# the session names of each entry copy, without the suffix
def entry_sessions(run):
    sessions = {}
    for root in run.glob("*/ROOT"):
        for name in SESSION.findall(read_text(root)):
            sessions[name.removesuffix(SUFFIX)] = root.parent.name
    return sessions


def theory_file(copy, theory):
    found = sorted(copy.rglob(theory + ".thy"))
    if len(found) != 1:
        raise ValueError(f"{theory}: {len(found)} files in {copy}")
    return found[0]


# the confirmed winners in one question log, in the order faster_step found them
def winners(log):
    with open(log) as f:
        rows = [r for r in csv.reader(f, delimiter="\t", quoting=csv.QUOTE_NONE) if len(r) >= 5 and r[1] == "linter_time"]
    for r in rows:
        p = props(r)
        if r[4] == "closes" and int(p["ms2"]) * SPEEDUP < int(p["ms"]):
            theory, lemma, offset = r[2].split(":", 3)[:3]
            _, old, new = r[3].split(" | ", 2)
            yield dict(theory=theory, lemma=int(lemma), copy_offset=int(offset), old=old, new=new,
                       ms=int(p["ms"]), ms2=int(p["ms2"]))


# copy() renamed the entry's own qualified names; undo it to map an offset back to the AFP text
def unrename(text, names):
    for name in names:
        text = text.replace(name + SUFFIX + ".", name + ".")
    return text


# the length of `by METHODS` at offset; the question log has line breaks as spaces
def step_length(text, offset, methods, what):
    pattern = r"by\s*" + r"\s+".join(map(re.escape, methods.split()))
    match = re.compile(pattern).match(text, offset)
    if not match:
        raise ValueError(f"{what}: no `by {methods}` at {offset}: {text[offset:offset + 60]!r}")
    return match.end() - offset


# -F applies one fix per lemma, the first one (Tool.apply_fixes): the others are not in the copy
def mark_applied(found):
    seen = set()
    for w in sorted(found, key=lambda w: (w["session"], w["theory"], w["copy_offset"])):
        w["applied"] = (w["theory"], w["lemma"]) not in seen
        seen.add((w["theory"], w["lemma"]))


def collect(run):
    sessions = entry_sessions(run)
    found = []
    for log in sorted((run / "logs").glob("*.tsv")):
        found += [dict(w, session=log.stem) for w in winners(log)]
    mark_applied(found)
    for w in found:
        place_original(run, sessions, w)
    for w in found:
        place_patched(run, w, found)
    return found


def place_original(run, sessions, w):
    entry = sessions[w["session"].removesuffix(SUFFIX)]
    names = [s for s, e in sessions.items() if e == entry]
    path = theory_file(run / entry, w["theory"].split(".")[-1])
    relative = path.relative_to(run / entry)
    original = read_text(AFP / entry / relative)
    copy_text = rename(original, names)
    w["length"] = step_length(copy_text, w["copy_offset"], w["old"], "copy")
    offset = len(unrename(copy_text[:w["copy_offset"]], names))
    step_length(original, offset, w["old"], "original")
    w.update(entry=entry, path=path, file=str(relative), offset=offset, line=line_of(original, offset),
             symbol=symbol_offset(original, offset), kind=kind(w["old"], w["new"]))


# edits applied earlier in the same file move the step
def place_patched(run, w, found):
    patched = read_text(w["path"])
    shift = sum(len("by " + o["new"]) - o["length"] for o in found
                if o["applied"] and o["theory"] == w["theory"] and o["copy_offset"] < w["copy_offset"])
    offset = w["copy_offset"] + shift
    step_length(patched, offset, w["new"] if w["applied"] else w["old"], "patched")
    w.update(patched_line=line_of(patched, offset), patched_symbol=symbol_offset(patched, offset))


# what copy() in lint_afp.py does to a theory's text
def rename(text, names):
    for name in names:
        text = re.sub(r"(?<![\w.])" + re.escape(name) + r"\.(?=\w)", name + SUFFIX + ".", text)
    return text


def clean(s):
    return re.sub(r"\s+", " ", s)


def write_winners(found, path):
    header = ["entry", "session", "theory", "file", "line", "offset", "symbol_offset", "original", "new",
              "original_ms", "new_ms", "kind", "applied", "patched_line", "patched_symbol_offset"]
    rows = [[w["entry"], w["session"].removesuffix(SUFFIX), w["theory"].split(".")[-1], w["file"], w["line"],
             w["offset"], w["symbol"], "by " + clean(w["old"]), "by " + clean(w["new"]), w["ms"], w["ms2"],
             w["kind"], "yes" if w["applied"] else "no", w["patched_line"], w["patched_symbol"]] for w in found]
    write_tsv(path, header, rows)


# census rows: session, file, symbol offset, command, seconds, text (linter_retime -I)
def write_retime(found, path, patched):
    header = ["session", "file", "offset", "command", "seconds", "text"]
    rows = []
    for w in found:
        if patched and w["applied"]:
            rows.append([w["session"], f"{PC_RUN}/{w['entry']}/{w['file']}", w["patched_symbol"], "by",
                         w["ms2"] / 1000, "by " + clean(w["new"])])
        elif not patched:
            rows.append([w["session"].removesuffix(SUFFIX), f"{PC_AFP}/{w['entry']}/{w['file']}", w["symbol"], "by",
                         w["ms"] / 1000, "by " + clean(w["old"])])
    write_tsv(path, header, rows)


def write_tsv(path, header, rows):
    lines = ["\t".join(map(str, r)) for r in [header] + rows]
    Path(path).write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    run, out = Path(sys.argv[1]), Path(sys.argv[2])
    found = collect(run)
    write_winners(found, out)
    if len(sys.argv) > 3:
        write_retime(found, Path(sys.argv[3]), patched=False)
    if len(sys.argv) > 4:
        write_retime(found, Path(sys.argv[4]), patched=True)
    applied = sum(w["applied"] for w in found)
    print(f"{len(found)} winners in {len({w['entry'] for w in found})} entries, {applied} applied by -F")
