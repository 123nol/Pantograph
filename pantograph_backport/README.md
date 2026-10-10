# Stage 4 companion delivery

Implemented on `client_centric_repo` over PR #1 merge
`0dd5d2225e2d093f66a4b6231c1aa35004f2c8f3`. The patch preserves the merged
server operations and custom model serializer. It adds the revision-2 descriptor,
real diagnostics, snapshot rollback, complete sequence parsing and checked
transition expressions.

- `repository_client_contract.patch`: complete Lean source/tests, capture utility
  and contract documentation relative to the exact merged base.
- `repository_client_contract.provenance.json`: source, patch, executable and
  toolchain identities plus verification outcomes.
- `live_capture/capture.json` and `live_capture/provenance.json`: 61 actual raw
  Mathlib exchanges, existing decoder acceptance, four exact canonical graph
  goldens, zero final allocations and confirmed process reaping.
- `../doc/repository_client_contract.md`: precise checked boundary and limitations.

`lake build repl Test.ContractFixtures` and `lake test` pass. The suite has
299 assertions, including 37 new Stage 4 assertions. The application codec,
PR #1 reconciliation, model and environment regressions have 316 passes.
Patch application to a clean exported base was checked and every resulting
source hash matches this checkout. No files were staged or committed.

The build reused an independently copied archive cache and rebuilt changed
source targets. This is Stage 4 local verification, not Stage 7 fresh release
reproduction. The imported Mathlib archive has no Git metadata; its expected
pin remains `29dcec074de168ac2bf835a77ef68bbe069194c5`.

The initial sandboxed diagnostic timed out while waiting for subprocess exit.
It is excluded from passed evidence. The final recorded capture ran outside the
sandbox and confirmed reaping.

Stages 5–8 remain pending. Production still uses its existing client. Transition
checks do not kernel-certify an assembled original theorem from independently
replayed search nodes. No fork publication, RL launch or production migration
was performed.
