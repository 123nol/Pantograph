# Recursion-depth exhaustion as a typed resource

Base: `client_centric_repo` at `ce8338e` (the merge of failure diagnostics,
source `661df4e32bb487f52e4bf229a34b155f9e69c76b`). Contract:
[transactional_resources.md](../../doc/transactional_resources.md), resource
details version 2.

## Reproduction

The post-#88 PUCT miniF2F run archived 60 failed attempts; 49 of them are
Lean's `maximum recursion depth has been reached` during `execute`
(`norm_cast` 39, `trivial` 6, `rfl` 2, `decide` 1,
`apply Finset.sum_range_succ_comm` 1). Each was answered as an unexpected
internal error and the worker was replaced.

`baseline-reproduction.json` runs the merged executable (built from `661df4e`)
with `Init` and `--maxRecDepth=200` on `(List.replicate 2000 0).length = 2000`.
`decide` exceeds the depth and the REPL answers
`{"error": "internal", "desc": "Unexpected REPL command failure", "recovery": "session-unusable"}`,
then exits; the following `stat` gets no response.

## After the change

`capture.json` (`scripts/test_transactional_resources.py --capture`, clean
tree, binary sha256 recorded in the file):

- the same `decide` returns `error: "resource"` with
  `resource: {version: 2, kind: "recursion-depth", phase: "execute", limit: 200}`
  and `recovery: "command-rolled-back"`; `stat` is unchanged, and
  `exact List.length_replicate 2000 0` on the same retained state is then
  certified by the kernel in the same session;
- a fixture that exhausts the depth through `withIncRecDepth`, and one that
  first closes the goal and then exhausts it, both roll back to the entry state;
- heartbeat exhaustion keeps its envelope, now with `version: 2`;
- a recursion failure inside `frontend.process` is reported by Lean's command
  elaborator as that command's error message, and the session continues.

`native-tests.log`: the Lean suite (431 assertions, including recursion-depth
rollback in every phase, repeated exhaustion without leaked allocations, and
inconclusive certification for both kinds) and the three raw executable
harnesses.

Not covered here: replaying the archived miniF2F bundles, which need the
pinned Mathlib runtime they were recorded with, and the 11 `fun_prop`
timeouts, which are a separate investigation.
