# isabelle_linter

A linter for Isabelle that checks every suggestion with the prover before showing it.

- **unused** finds what a lemma doesn't need: facts, `have` steps, `apply` lines and assumptions.
- **faster_step** finds `by` steps that another method proves faster. It tries other methods,
  the step without each of its facts, for `by M1 M2` the fastest method for each subgoal, and
  `simp only:` with the rewrite rules the step's proof used.
- **simp_hygiene** finds `[simp]` rules, simprocs and classical rules that are tried often for
  nothing. It needs a patched Isabelle (below) and only reports.

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

`-l unused` or `-l faster_step` runs just one lint (simp_hygiene runs too where it can). By
default faster_step only tries steps over 1 second (`-o faster_step_slow=SECONDS`).

`-o faster_step_try0=true -o linter_log=FILE` also runs Isabelle's try0 on each step faster_step
tries and re-times its proof the same way, as a baseline in the question log; it never changes
the findings.

Assumptions are reported but never removed by `-F`, since removing one changes the lemma's
statement.

## Simp hygiene

`simp_hygiene` finds rules that the simplifier and the classical reasoner keep trying for
nothing. Every lemma of the session is run once with the rules counted: how often the
simplifier's net offers each `[simp]` rule, how often it matches and rewrites, how often a
conditional rule's condition fails and the time that takes, each simproc's calls, rewrites and
time, and how often `auto`, `fast`, `force` ... try each classical rule and `blast` is offered
it. Of what is tried at least 1000 times in the session (`-o simp_hygiene_min`), it reports

- `[simp]` rules that never rewrote, and simprocs that never rewrote;
- conditional `[simp]` rules whose condition held in at most 10% of its tries;
- classical rules in the proofs of at most 5% of the lemmas that try them.

```
Simp_Hygiene.thy:23: [simp_hygiene] [simp] rule `Simp_Hygiene.pair_same` offered 445 times in 9 lemmas, never matched, never rewrote
  declared here: drop [simp], or `declare Simp_Hygiene.pair_same [simp del]` where it is not needed
  information only, nothing was re-run without it; counted over 25 of 25 lemmas
```

Stock Isabelle cannot count this: its simplifier trace hooks only see rules that already matched,
and the classical reasoner has none. The lint needs an Isabelle with `etc/simpstats.patch`, which
adds a `rule_statistics` option (off by default); a release would need it upstream:

```bash
cp -a Isabelle2025-2 Isabelle2025-2-simpstats && cd Isabelle2025-2-simpstats
patch -p1 < ~/dev/isabelle_linter/etc/simpstats.patch
echo -n Isabelle2025-2-simpstats > etc/ISABELLE_IDENTIFIER    # own heaps, apart from the release's
bin/isabelle linter -d ~/dev/isabelle_linter/test -o simp_hygiene_min=100 Linter_Simp_Hygiene
```

Its findings are information only and never part of `-F`: removing `[simp]` or `[intro]`
changes every later proof, also in other sessions and in commands that are not lemmas, which
only a rebuild checks. Only lemmas are counted, not `fun`, `datatype` or other commands, and
only rules with a name: the equations of `fun` and `primrec` reach the simpset without one and
are left out.

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
