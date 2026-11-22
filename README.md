# isabelle_linter

A linter for Isabelle. Every suggestion is checked by the prover before you see it.

```
Unused.thy:18: [unused] not needed:
  `have h1 : "length (xs @ ys) = length xs + length ys"` and its proof (line 20)
  fact `using h1` (line 22)

Example.thy:9: [faster_step] `by (simp add: distrib_left)` takes 1 ms instead of 53 ms for `by (smt (verit) distrib_left)`
```

## Lints

- **unused**: facts, `have`s, `apply`s and assumptions a lemma doesn't need.
- **faster_step**: `by` steps another method proves faster.
- **diagnostic_commands**: `nitpick`, `value`, `find_theorems` and friends that run on every build but prove nothing.
- **unused_imports**: imports that can go. Checked by building an edited copy of the session.
- **datatype_plugins**: datatype plugins nothing uses.
- **fun_to_primrec**: `fun`s that could be `primrec`.
- **simp_scope**: `[simp]` rules set wider than the steps need.
- **simp_hygiene**: simp and classical rules tried often for nothing. Needs a patched Isabelle, see below.

## Setup

You need Isabelle2026. For Isabelle2025-2, use the `isabelle2025-2` branch.

```bash
isabelle components -u ~/dev/isabelle_linter
isabelle scala_build
```

## Running it

```bash
isabelle linter -d DIR SESSION              # report
isabelle linter -F -d DIR SESSION           # also apply the fixes
isabelle linter -l unused -d DIR SESSION    # one lint
isabelle linter -d test -o faster_step_slow=0 Linter_Example    # the examples
```

`-F` never removes assumptions, since that changes the statement. faster_step and simp_scope
skip anything under a second; lower that with `-o faster_step_slow=0.1` or `-o simp_scope_slow=0.1`.

For simp_hygiene, patch a copy of Isabelle:

```bash
cp -a Isabelle2026 Isabelle2026-simpstats && cd Isabelle2026-simpstats
patch -p1 < ~/dev/isabelle_linter/etc/simpstats.patch
echo -n Isabelle2026-simpstats > etc/ISABELLE_IDENTIFIER
```

## Other tools

- `isabelle linter_census` shows where a build's checking time went, from its stored timings.
- `isabelle linter_retime` times the slowest steps again, one at a time.
- `isabelle linter_collect` records which methods close each step, and how fast.

## Parent sessions

A theory that is not in one of a session's parent heaps is checked again by every session that
imports it through `sessions`. `isabelle linter_parent` reads which theories each session checked,
and for how long, from the build logs, and suggests the parent that would hold the most of that
time in its heap. The new parent keeps every current ancestor and does not import the session, so
the edit is one line of ROOT.

```bash
isabelle build -d test -o build_timing_threshold=0 Linter_Parent_Lib Linter_Parent_Client
isabelle linter_parent -d test -m 0 Linter_Parent_Client
```

```
Linter_Parent_Client: parent Linter_Parent_Lib instead of HOL saves 0.2 s of 0.2 s re-checked (0.3 s stored)
  test/ROOT:15: session Linter_Parent_Client in "parent/client" = Linter_Parent_Lib +
  now ancestors, may leave `sessions`: Linter_Parent_Lib
  Linter_Parent_Lib will store a heap
```

With that edit the client checks nothing of the library again. On the AFP build logs of
2026-10-01 it finds 33.8k s of the 260k s of AFP command time, about 13%:

```bash
isabelle linter_parent -d AFP -L LOGDIR -m 100
```

The heap content of a session is what it and its ancestors checked, so a parent needs a log
database too. `-L DIR` reads the databases from a directory instead of the heap store, `-O FILE`
writes every suggestion as TSV, and `-m SECONDS` hides the small ones (default 1 s). Each
suggestion assumes the other sessions keep their parents.

## Other provers

`xlint/` is a prover-independent core for the same lints, written in Rust. A prover takes part
through a small server that answers three JSON-line requests (hello, load, ask). `provers/lean` is
the server for Lean 4.

```bash
(cd provers/lean && lake build) && (cd xlint && cargo build)
cd MATHLIB    # the server runs in the target project's environment
lake env xlint -s xlint-lean FILE.lean                          # lint
lake env xlint census -s xlint-lean -O census.tsv FILE.lean     # where the time goes
lake env xlint retime -s xlint-lean -I census.tsv -n 100        # the slowest steps again, alone
```

`-j N` lints N files at once, each with its own server (default: the cores but two). Reports and
the question log keep the order of the files. With more than one file at a time the times are
taken under load, and the first row of the log says so; `census` and `retime` run one file at a
time.

```bash
xlint run -d OUT -p PROJECT -s SERVER -b CHECK -t 600 -f FILES    # a corpus, on a copy of PROJECT
```

`xlint run` lints the listed files with `-F` on a copy of the project, runs `CHECK FILE` on each
fixed file and puts back a file that fails. `OUT/summary.tsv` has a row per file and their total,
with the columns `scripts/unused_summary.py` prints for Isabelle. A file with a row is skipped on
the next run. `-x TOOL` takes another linter that prints findings the same way, such as
`xlint-mizar`.

The census TSV has the columns of `isabelle linter_census -O`. A `step` row is a tactic that closes
its goal, timed once more on that goal, so its time is also inside the row of its theorem.

Every lint runs on Lean 4.36.0. On six Mathlib v4.36.0 files (510 commands, 252 closing steps) the
census takes 44 s on a laptop. Steps hold 14% of the commands' time, the ten slowest steps 40% of
step time, and `simp` and `simpa` two thirds of it. The 30 slowest steps take 2.8 s in the census
and 3.1 s re-timed alone (three runs, medians).

`provers/rocq` is the server for Rocq 9.2. It links Rocq's own libraries and keeps the state
before every sentence, so a question starts at its lemma.

```bash
(cd provers/rocq && opam exec --switch rocq -- dune build)    # a switch with rocq-prover and yojson
opam exec --switch rocq -- xlint -s provers/rocq/_build/default/main.exe FILE.v
```

It answers `unused`, `unused_imports`, `faster_step`, `diagnostic_commands`, `census` and `retime`.
The pieces of `unused` are tactic sentences, the lemmas after `using`, hint databases and `rewrite`
rules. A step is a tactic sentence that leaves fewer goals. Only proofs that end in `Qed` are
checked, and a `Require Export` is reported but kept.

On six standard library files (Bool, Compare_dec, EqNat, List, Permutation, Wf_nat; 6,603 lines,
624 proofs checked) the census takes 5 s on a laptop: 5,456 sentences in 1.9 s, 960 closing steps
in 0.7 s, and the ten slowest steps half of the step time. `unused` deletes 69 tactics and 4
`assert`s in 58 proofs, 7.6 per 100 steps, and `unused_imports` four modules in three files. The
files compile with every fix. `faster_step` finds nothing with steps of 20 ms or more searched.
The four lints take 28 s.

Mizar is compared through its own tools. `provers/mizar/xlint-mizar ARTICLE.miz...` runs relprem,
relinfer, reliters, trivdemo, chklab and inacc (printed as `unused`) and irrths and irrvoc
(`unused_imports`) on a copy of each article. It needs `MIZFILES` and the Mizar programs on `PATH`;
Mizar 8.1.15 unpacks from its i386 tarball into `~/opt/mizar` without root. On `xboole_1` of MML
5.106.1517 (116 theorems, 406 steps) the tools report 25 irrelevant inferences and one reference
that can move, in 1.6 s.

### Samples

`unused` on random files of each library (`random.Random(1).sample` of the sorted file names), run
with `xlint run` on a laptop, several files at once, so the times were taken under load. The
Isabelle row is the 93 finished entries of the AFP sample.

| corpus | files | lemmas | steps | per lemma | lemmas with a finding | pieces per 100 steps | timed fixes |
|---|---|---|---|---|---|---|---|
| Isabelle AFP | 93 entries | 24,208 | 96,718 | 4.0 | 22.1% | 15.0 | 2,156 -> 2,194 s |
| Lean Mathlib v4.36.0 | 197 of 200 | 2,133 | 3,598 | 1.7 | 8.2% | 7.9 | 55.9 -> 51.3 s |
| Rocq 9.2 standard library | 149 of 150 | 2,825 | 6,093 | 2.2 | 12.2% | 9.7 | 16.2 -> 16.2 s |
| Mizar MML 5.106.1517 | 68 of 100 | 3,178 | 42,256 | 13.3 | | 6.3 | |

- Mathlib: 278 lemmas of `simp` lists and 8 `have`s go. Three files do not pass `lean FILE` as
  written, so their fixes are unchecked and left out. All other fixed files pass.
- Rocq: 552 tactic sentences, 22 `using` lemmas and `rewrite` rules, 16 `assert`s and 2 hint
  databases go. Every fixed file compiles, and one file ran over 300 s.
- Mizar: 2,502 irrelevant inferences (relinfer), 157 references that can move (reliters), 6
  justifications that can be straightforward and 3 inaccessible items. relprem reports nothing.
  32 articles ran over 300 s, which leaves out the longest ones.

What is counted differs between the provers, so the rows cannot be compared directly:

- A lemma is an Isabelle lemma the linter checked, a Lean `theorem` or `lemma` with a `by` proof, a
  Rocq proof that ends in `Qed`, and a Mizar `theorem`.
- A step is an Isabelle `by` or `apply`, a Lean tactic that closes its goal, a Rocq tactic sentence
  that leaves fewer goals, and a Mizar `by`.
- A piece is a fact, `have` or `apply` in Isabelle; a `simp` list lemma or a `have` in Lean, where
  `rw` lists and term proofs are not searched; a tactic sentence, `using` lemma, `rewrite` rule or
  hint database in Rocq; and one hit of a Mizar tool.
- Isabelle, Lean and Rocq pieces were removed together and the result checked again. Mizar's hits
  are its tools' reports, with nothing removed, and several can fall in one theorem, so the row has
  no share of lemmas.

## How it works

The session is checked once in PIDE, like in jEdit. Each question ("does this lemma still work
without `h1`?") goes to the prover as an overlay, so only that lemma runs again. Lints live in
`src/lints/`; see `Lint` in `src/core/pide.scala` to write one.
