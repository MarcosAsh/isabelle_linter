# isabelle_linter

A linter for Isabelle that checks every suggestion with the prover before showing it.

- **unused** finds what a lemma doesn't need: facts, `have` steps, `apply` lines and assumptions.
- **faster_step** finds `by` steps that another method proves faster. It tries other methods,
  the step without each of its facts, and for `by M1 M2` the fastest method for each subgoal.

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

Assumptions are reported but never removed by `-F`, since removing one changes the lemma's
statement.

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

## How it works

The session gets checked once in a PIDE session, the same machinery jEdit uses. Each question,
like "does this lemma still work without `h1`?", goes to the prover as an overlay, so only that
lemma is re-run and nothing else gets re-checked.

The lints are in `src/lints/`. A lint asks questions in rounds and turns the answers into
findings; see `Lint` in `src/core/pide.scala` to write your own.
