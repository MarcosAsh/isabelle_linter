# isabelle_linter

A linter for Isabelle that checks its suggestions with the prover. For now it has one lint,
`faster_step`, which finds `by` steps that another method proves faster.

```
Example.thy:12: `by simp` checks in 2 ms instead of 27 ms for `by (metis append_assoc rev_append)`
```

## Setup

You need Isabelle2025-2.

```bash
isabelle components -u ~/dev/isabelle_linter
isabelle scala_build
```

## Running it

```bash
isabelle linter -d test -o faster_step_slow=0 Linter_Example   # the example
isabelle linter -d DIR SESSION                                  # your own session
```

By default only steps over 1 second are tried. You can change that with
`-o faster_step_slow=SECONDS`.

## How it works

The theories get checked once in a PIDE session (the same machinery jEdit uses). Each "try
method X on this step" goes to the prover as an overlay on the step's goal, so nothing else gets
re-checked. The lint itself is in `src/lints/faster_step/`, and `src/core/pide.scala` has the
small interface for writing other lints on top of it.
