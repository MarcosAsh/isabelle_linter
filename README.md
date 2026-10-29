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

## How it works

The session is checked once in PIDE, like in jEdit. Each question ("does this lemma still work
without `h1`?") goes to the prover as an overlay, so only that lemma runs again. Lints live in
`src/lints/`; see `Lint` in `src/core/pide.scala` to write one.
