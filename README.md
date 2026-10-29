# isabelle_linter

A linter for Isabelle that checks every suggestion with the prover before showing it.

- **unused** finds what a lemma doesn't need: facts, `have` steps, `apply` lines and assumptions.
- **faster_step** finds `by` steps that another method proves faster. It tries other methods,
  the step without each of its facts, for `by M1 M2` the fastest method for each subgoal, and
  `simp only:` with the rewrite rules the step's proof used.
- **diagnostic_commands** finds commands that prove nothing but are checked on every build:
  `nitpick`, `quickcheck`, `sledgehammer`, `find_theorems`, `thm`, `value`, `export_code` and
  the rest of kind `diag`, each with the time it took when the session was checked.
- **simp_hygiene** finds `[simp]` rules, simprocs and classical rules that are tried often for
  nothing. It needs a patched Isabelle (below) and only reports.
- **unused_imports** finds theory imports that can go, checked by building an edited copy of the
  session.
- **datatype_plugins** finds `datatype` plugins (code, size, quickcheck, ...) whose content nothing
  later uses, and deletes them with `(plugins del: ...)` if that makes the datatype faster.
- **fun_to_primrec** finds `fun` definitions that `primrec` can make, without proving the patterns
  and termination, if nothing later uses the facts only `fun` makes (`f.induct`, `f.elims` ...).
  It also reports a slow `fun` that stays (`-o fun_slow=SECONDS`, default 5).
- **simp_scope** finds simp rules set above the steps that don't need them: a `note
  simps[simp] = ...` in a proof loses its `[simp]`, and each step gets only the theorems it
  needs as `simp add:`. A step's own `simp add:` bundle, like `c_defs`, is cut down the same way.

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

`-l unused`, `-l faster_step` or `-l simp_scope` runs just one lint. By default faster_step only
tries steps over 1 second (`-o faster_step_slow=SECONDS`).

`-o faster_step_try0=true -o linter_log=FILE` also runs Isabelle's try0 on each step faster_step
tries and re-times its proof the same way, as a baseline in the question log; it never changes
the findings.

Assumptions are reported but never removed by `-F`, since removing one changes the lemma's
statement.

## Diagnostic commands

```bash
isabelle linter -d test -l diagnostic_commands Linter_Example
```

A diagnostic command leaves the proof state as it was, so deleting one cannot change a theorem.
`-F` deletes only proof and counterexample search (`nitpick`, `quickcheck`, `sledgehammer`,
`try`, `try0`, `solve_direct`, `find_*`, ...), with its `lemma ... oops` if that is all the lemma
does. `value`, `export_code` and the like may be tests: the advice is to move them to a test
session, so that sessions importing this one do not wait for them, and `-F` leaves them. A search
with `expect =` is a test too, as is every search of a tool whose `*_params` set `expect`
somewhere in the session. `thm`, `term`, `print_*` and other printing commands are reported only.

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
only a rebuild checks. Only lemmas are counted, not `fun`, `datatype` or other commands. The
equations of `fun` and `primrec` reach the simpset without a name, so they are counted together
under their constant.

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
it. Imports that break a theory, or change what it exports (`export_theory`: types, constants,
theorem statements, instances), are put back, and what is reported is a set of removals the copy
built with. Sessions in other directories that build on the session are listed but not built.
`-F` removes the imports, and adds any theory that only those imports kept in the session to the
ROOT's theories.

Only imports of theories outside the Isabelle distribution are tried, unless
`-o unused_imports_distribution`. The report gives the time of each theory's commands and the
session's critical path (the longest chain of imports) before and after, from one build each.

## Definitions

The definition lints read the text after a definition: the rest of its theory, the theories that
import it, and the sessions built on its session (in the `-d` directories). A plugin stays if that
text names something it makes, or may use it without naming it (`value` uses code, a `fun` on the
type uses size, ...). Their fixes can still break a later theory, so check them by building the
session and every session built on it, on a copy:

```bash
isabelle linter -l datatype_plugins,fun_to_primrec -o fun_slow=0.3 -d test Linter_Example
```

## Simp scope

```bash
isabelle linter -l simp_scope -d test Linter_Example
```

simp_scope only tries lemmas that take a second (`-o simp_scope_slow=SECONDS`). It asks each step
which theorems of the notes' facts and of its own simp facts its proof used, drops them one at a
time while the step still closes alone, then re-runs the whole lemma with the narrower rules. The
fix is kept only if the lemma gets faster (medians of 3 runs alone, `-o simp_scope_speedup=1.2`).
`declare` and `lemmas` outside proofs are left alone, as other theories see them too;
`-o simp_scope_theory=true` reports those that at most half of the later lemmas in their theory
need.

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

## How it works

The session gets checked once in a PIDE session, the same machinery jEdit uses. Each question,
like "does this lemma still work without `h1`?", goes to the prover as an overlay, so only that
lemma is re-run and nothing else gets re-checked.

The lints are in `src/lints/`. A lint asks questions in rounds and turns the answers into
findings; see `Lint` in `src/core/pide.scala` to write your own.
