# Elaboration-abort and failure-diagnostic evidence

Base: `client_centric_repo` at `9512761` (the merge of compiler-aware
validation, source `fc740c26a1e832ecb571859af24a5c632a351bd9`). Contract:
[failure_diagnostics.md](../../doc/failure_diagnostics.md).

## Reproduction

The PUCT/no-PLN run of 6 November had 74 remote internal errors. The console
shows only `PantographRemoteInternalError; replacing Pantograph worker`, so the
failing requests are not in the log.

`baseline-reproduction.json` runs the merged executable (sha256
`6cba4f74fdf2bc8ba7060603e7bc11feffb7229dd8c288ec7c3c0ba2e9c2ef29`, the companion
pinned by client `e8aa9ec`) on `True` with each of:

- `exact (fun (x : Nat) => True.intro) _`
- `refine (fun (x : Nat) => True.intro) _`
- `have h := (fun (x : Nat) => x) _`
- `exact (_ : True)`

Every one returns `Unexpected REPL command failure` with `session-unusable`
and the process exits. Each is an ordinary Lean error ("don't know how to
synthesize placeholder") that Lean signals with an abort exception.

The run's log supports this as a major source: it has 2,478 failed `exact`,
394 failed `refine` and 106 failed `have` attempts, but not one "don't know how
to synthesize" message, although unresolved implicit arguments are one of the
most common reasons a sampled lemma application fails. The log cannot say how
many of the 74 errors had this cause; the diagnostic below records the rest.

## After the change

`capture.json` (`scripts/test_failure_diagnostics.py --mathlib ... --capture`):

- the four tactics return ordinary `tacticErrors` with Lean's message, the same
  state is then closed by `trivial` and certified, and `stat` returns to zero,
  both with `Init` and with the pinned Mathlib;
- an injected internal failure and an unrenderable error each give one stdout
  `internal` response, exit, and one stderr record with
  `repl_command_sequence: 3` and the right operation, state, goal, phase and
  category;
- an ordinary rejection leaves the session usable and writes no record.
