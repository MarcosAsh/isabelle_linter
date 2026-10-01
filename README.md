# isabelle_linter

A linter for Isabelle that checks every suggestion with the prover before showing it.

- **unused** finds what a lemma doesn't need: facts, `have` steps, `apply` lines and assumptions.
- **faster_step** finds `by` steps that another method proves faster.

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

## How it works

The session gets checked once in a PIDE session, the same machinery jEdit uses. Each question,
like "does this lemma still work without `h1`?", goes to the prover as an overlay, so only that
lemma is re-run and nothing else gets re-checked.

The lints are in `src/lints/`. A lint asks questions in rounds and turns the answers into
findings; see `Lint` in `src/core/pide.scala` to write your own.
