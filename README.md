# isabelle_linter

A linter for Isabelle that checks every suggestion with the prover before showing it.

- **unused** finds what a lemma doesn't need: facts, `have` steps, `apply` lines and assumptions.
- **faster_step** finds `by` steps that another method proves faster. It tries other methods,
  the step without each of its facts, for `by M1 M2` the fastest method for each subgoal, and
  `simp only:` with the rewrite rules the step's proof used.
- **unused_imports** finds theory imports that can go, checked by building an edited copy of the
  session.

```
Unused.thy:18: [unused] not needed:
  `have h2 : "rev [] = ([] :: nat list)"` and its proof (line 21)
  fact `using h1` (line 22)
  `have h1 : "length (xs @ ys) = length xs + length ys"` and its proof (line 20)

Example.thy:9: [faster_step] `by (simp add: distrib_left)` takes 1 ms instead of 53 ms for `by (smt (verit) distrib_left)`
```

## Setup

You need Isabelle2025-2.

```bash
isabelle components -u ~/dev/isabelle_linter
isabelle scala_build
```

## Running it

```bash
isabelle linter -d test -o faster_step_slow=0 Linter_Example   # the examples
isabelle linter -d DIR SESSION                                  # your own session
isabelle linter -F -d DIR SESSION                               # also apply the fixes
```

`-l unused` or `-l faster_step` runs just one lint. By default faster_step only tries steps
over 1 second (`-o faster_step_slow=SECONDS`).

`-o faster_step_try0=true -o linter_log=FILE` also runs Isabelle's try0 on each step faster_step
tries and re-times its proof the same way, as a baseline in the question log; it never changes
the findings.

Assumptions are reported but never removed by `-F`, since removing one changes the lemma's
statement.

## Unused imports

`-l unused_imports` finds theory imports that can go, either because another import brings the
theory in anyway or because nothing in the session needs it.

```bash
isabelle linter -l unused_imports -d test Linter_Imports
```

The prover says which theories each theory uses: whose theorems its proofs use, whose constants,
types, classes and type instances it mentions, and whose names its text refers to. An import is
proposed if every theory of the session still has those without it. Notation and other implicit
uses don't show up there, so the proposals are checked by building a copy of the session's
directory (sessions renamed `*_Imports`), together with the sessions of the same ROOT that build on
it. Imports that break a theory are put back, and what is reported is a set of removals the copy
built with. Sessions in other directories that build on the session are listed but not built.

Only imports of theories outside the Isabelle distribution are tried, unless
`-o unused_imports_distribution`. The report gives each theory's checking time and the session's
critical path (the longest chain of imports) before and after, from one build each.

## Collecting data

`isabelle linter_collect` records, for every `by` step of a session, the goal and which
methods close it and how fast. It is the data for learning which method to try first.

```bash
isabelle linter_collect -d ~/afp/thys -O Huffman.jsonl Huffman    # one AFP entry; list all its sessions
```

Each line is one step: the goal's features (head constant, constants, size, ...), and for every
method whether it closes the goal within 2 seconds (`-o collect_timeout`), with the median of 3
re-timed runs for the ones that do. The methods that close are re-timed a few steps at a time, so
the times are not distorted by the rest of the run. `-o collect_sledgehammer=SECONDS` also runs
Sledgehammer on each step. If the output file exists, the command does nothing, so a loop over
many entries can be restarted.

## Where the time goes

`isabelle linter_census` reads the command timings that `isabelle build` stored and shows
which commands the checking time goes to. `isabelle linter_retime` then times the slowest `by`
steps again, one at a time, since build timings come from a loaded machine.

```bash
isabelle build -d AFP -D AFP/Huffman -o build_timing_threshold=0.01
isabelle linter_census -d AFP -D AFP/Huffman -O timings.tsv
taskset -c 0-11 isabelle linter_retime -d AFP -I timings.tsv -n 200 -O retime.tsv
```

`-P profiles.tsv` also runs each step once under Poly/ML's profiler and keeps its busiest ML
functions, which shows where a slow step spends its time.

## How it works

The session gets checked once in a PIDE session, the same machinery jEdit uses. Each question,
like "does this lemma still work without `h1`?", goes to the prover as an overlay, so only that
lemma is re-run and nothing else gets re-checked.

The lints are in `src/lints/`. A lint asks questions in rounds and turns the answers into
findings; see `Lint` in `src/core/pide.scala` to write your own.
