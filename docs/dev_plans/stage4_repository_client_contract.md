# Stage 4: repository-owned client companion contract

Status: architecture verified by the user and Stage 4 implemented on 2026-10-10.
The implementation and checked boundary are documented in
[the companion contract](../../doc/repository_client_contract.md). Evidence and
patch delivery are recorded in `pantograph_backport/`.

## Source and scope

Implement on `client_centric_repo` in `/home/nolawi/pantograph_fork`, whose
clean initial HEAD is `0dd5d2225e2d093f66a4b6231c1aa35004f2c8f3`, the merged
PR #1 source required by the application plan. Retain Lean
`leanprover/lean4:v4.10.0-rc1` and the existing dependency pins.

This adds checked transition expressions as a supported execution contract.
Shared tactic execution, diagnostics, rollback, and validation must cover every
existing Lean caller. The selected-parent scan alone cannot supply this contract.

Preserve omitted goal selection defaulting to zero, explicit nonzero selection,
automatic sibling resumption, conversion finalization, calc and structured
operations, and the existing message/fragment fields. Preserve the custom model
serializer, local context indices, binder metadata, expression strings and graph
schema. Stage 4 ends at a tested companion executable and raw decoder evidence.

## Execution architecture

1. Add the exact revision-2 `protocol.describe` descriptor and a successful
   transition validation value in `Pantograph/Protocol.lean`. Metadata contains
   only `version=1`, `scope=transition-expressions`, and `checked=true`. Admission
   and unsafe flags remain at the response top level. Failures carry false flags
   without successful validation evidence.
2. Introduce one shared transaction mechanism for goal operations in
   `Pantograph/Goal.lean`, with small dedicated diagnostic/validation modules
   where needed. Capture the caller's complete elaborator/meta/core snapshot,
   restore the requested goal snapshot, isolate request messages, execute,
   collect diagnostics, and save a successful result snapshot. Restore the caller
   snapshot and outer message log on every exit. Logged errors reject execution
   even when the operation returned normally; thrown failures retain available
   diagnostics. No failed operation allocates a published state.
3. Migrate all goal operations and callers to that transaction mechanism:
   string tactics, assignment, have/let/define, motivated application,
   no-confusion, conversion entry/exit and calc. Update result types and all
   matching Lean callers together. Conversion finalization must accumulate the
   same request diagnostics rather than losing the inner operation's messages.
4. Parse complete tactic sequences with the pinned Lean parser, preserving
   tactic versus conversion parsing according to the selected goal. Ordinary
   multiline sequences work; trailing nonconsumed input produces parse failure.
   Term-based operations continue to require complete term parsing.
5. Validate the finalized result before serialization and allocation in
   `Repl.lean`. Compare input and output metavariable contexts, inspect new or
   changed expression and delayed assignments, and traverse their reachable
   dependencies. Include the selected goal, changed coupled goals, retained
   obligations, relevant local types/let values, and reachable declarations
   introduced since the input snapshot. Resolve assignments using the pinned
   Lean APIs. Scan elaborated expressions for admissions and resulting proof
   dependencies for unsafe declarations. Stop recursive declaration expansion
   at the input environment, which remains the imported trust basis; inspect
   directly used unsafe constants there. Track visited dependencies to terminate
   traversal.
6. Preserve unresolved reachable obligations and their dependencies, including
   synthetic/delayed obligations that tactics omitted from the visible goal list.
   Keep intentional dormant sibling and conversion obligations consistent with
   the merged resumption contract. An unchanged open goal after `skip` is valid.
   Missing declarations, uninspectable changed assignments, or an apparent
   completion with unresolved obligations produce a named `validation` command
   error if the obligations cannot be represented safely. Never turn missing
   evidence into negative safety flags.
7. Render real Lean diagnostics using the merged `kind`, `severity`, `pos`,
   `data`, and optional `endPos` schema. Use source positions from the actual
   parsed request when available; otherwise use exactly `(0, 0)`. Include
   warnings and information on success and diagnostics on parse/tactic failure.
   Keep `tacticErrors` as the sole string-array execution failure indicator.

The exact delayed-assignment and synthetic-obligation implementation will follow
an audit of the installed Lean 4.10 sources. Any required architectural change
to this checked boundary must be reported before reducing its coverage.

## Alternatives considered

| Approach | Benefit | Cost or defect | Decision |
| --- | --- | --- | --- |
| Shared transaction and expression validator | Covers library and REPL callers with one execution contract | Requires migrating result types and existing tests | Chosen |
| Add checks only in the REPL handler | Smaller initial diff | Library callers retain logged-error and rollback defects | Rejected |
| Keep selected-parent/direct-constant flags | Preserves the smallest merged implementation | Misses coupled assignments, local values, hidden obligations and introduced dependencies | Rejected |
| Audit all imported declarations or kernel-certify reconstructed roots | Broader proof assurance | Expands beyond transition checks and the fixed imported trust basis | Separate feature |
| Reapply the older backport or accept both schemas | Reuses historical code | Risks reverting PR #1 and creates competing contracts | Rejected |

## Verification and delivery

Run `lake build repl` and `lake test`, retaining all merged tests and migrating
exact success expectations to the new metadata. Add meaningful shared-operation
and protocol tests for valid tactics; multiline and trailing-input parsing;
type/thrown failures; logged-error followed by `trivial`; warnings/information
and source positions; message isolation; assignment/environment rollback;
direct/nested/local/introduced-declaration admissions; positive unsafe scanning;
ordinary tactics using internal metaprogramming; `skip`; coupled assignments;
delayed obligations; hidden holes; omitted/nonzero indices; conversion and calc.
Positive unsafe tests must reach the scanner, rather than fail elaboration first.

Use an independent local build cache copied from the reference archive when
necessary, leaving the downloaded source and executable intact. Record cache
reuse as diagnostic build evidence, not Stage 7 fresh-build reproduction.

Capture raw line-delimited JSON exchanges from the patched executable using
explicit Lake paths and `stdbuf -oL`. Run the existing revision-2 pure decoder
against actual descriptor, success and rejection payloads. Compare model-bearing
fields and canonical graph expectations without changing historical fixtures.
Record initial/final state counts, subprocess reaping, base commit, source patch
hash, executable hash, toolchain/compiler identity, imports, options and test
commands/results. Verify patch application against the exact clean base.

Produce `repository_client_contract.patch`, a provenance descriptor, raw fixture
captures and a Stage 4 handoff. Prepare these in this writable checkout. Their
specified application destination is
`/home/nolawi/new-maths/maths_ai/gnn_inference/pantograph_backport/` and associated
fixture directories; copying there requires filesystem approval because those
paths are outside the session's writable roots.

Update the handoff status only after the Stage 4 gate passes. Keep Stage 5 live
client ownership/model probes, Stage 6 application migration, Stage 7 release
reproduction and Stage 8 deployment gates pending. External publication and RL
launch are outside this assignment.
