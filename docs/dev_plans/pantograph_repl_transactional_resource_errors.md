# Transactional resource errors in the custom Pantograph REPL

Status: local REPL implementation and host verification completed 2026-11-04
on `feat/transactional-resource-errors`, based on `9ecaaea`. Companion client,
application, Docker, and JupyterHub delivery gates remain pending. No deployed
executable was replaced.

Implementation evidence: [revision-3 contract](../../doc/transactional_resources.md)
and [handoff](../../pantograph_backport/transactional_resources/README.md).
The host build, 351 native assertions, and 22 captured raw executable exchanges
pass. Staging uses a separate Core state reference, so rollback discards staged
references instead of running a restoration procedure under exhausted budgets.

Companion: [Standalone client resource errors and recovery](pantograph_client_resource_errors_and_recovery.md).
Implement the common wire contract in both repositories before deploying the
new client. Application integration is an explicit delivery gate in the
companion plan.

## Objective and observed failure

A JupyterHub MCTS training run received these final REPL stdout lines:

```text
Uncaught IO exception
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

The client then raised `PantographProtocolError: Unsolicited REPL stdout`.
`whnf` is Lean's weak-head reduction operation. The heartbeat limit bounds
computational work, rather than elapsed seconds. The log establishes that a
heartbeat exception escaped request processing. It does not establish the
triggering tactic or the failing processing phase.

The scope change is that resource exhaustion becomes a first-class command
outcome across execution, observation, and response construction. Shared
command handling must preserve allocation ownership and protocol framing when
any of those phases fails. Merely catching exceptions around tactic execution
does not cover failures while rendering diagnostics or serializing goals.

The success criteria are one structured response for a recoverable command,
unchanged previously issued snapshots after rollback, and explicit session
termination whenever recovery cannot be established. Lean validation and
kernel certification remain mandatory.

## Source basis and implementation location

The inspected current companion source is `123nol/Pantograph`,
`client_centric_repo`, at `9ecaaea242f427e534aff29314513c358b4d21ad` in an
isolated reference checkout, `/tmp/pr72-repl`. It implements protocol revision
2. The separate `/home/nolawi/pantograph_fork` checkout is at the older
`fe57f98d85a3fb6b9bdd32f9e725bdda1c721449`. Do not implement against that older
checkout without first integrating the newer snapshot/certification changes.

Develop on a branch of the maintained fork or an isolated worktree based on its
verified current head. Do not edit the downloaded JupyterHub binary in place.
Recheck source revisions and local changes before implementation.

Relevant inspected files:

- `Main.lean`: one long-lived `CoreM` loop; the outer IO catch prints two plain
  stdout lines and exits.
- `Repl.lean`: command dispatch and allocation registration. Successful
  `goal.tactic` processing also validates and serializes results outside the
  inner tactic-operation catch.
- `Pantograph/Goal.lean`: `GoalState.withOperation` isolates tactic work, but
  error/message rendering can itself execute Lean computations.
- `Pantograph/Library.lean`: constructs the outer Lean context.
- `Pantograph/Protocol.lean`: descriptor and wire structures.
- `Pantograph/Certify.lean`: separate proof-certification budget and outcomes.
- `Test/`, `doc/`, and `pantograph_backport/`: native tests, contracts, and handoff.

Lean 4.10.0-rc1 `CoreM.toIO` establishes a heartbeat origin when entering the
outer computation. `Main.lean` enters that computation once for the complete
loop. There is no explicit per-command heartbeat reset at that boundary.
Audit restored contexts before deciding how much of the observed consumption
was cumulative. Do not describe the incident as a proven expensive single
tactic until a request trace demonstrates it.

## Alternatives considered

| Approach | Benefits | Limitations | Decision |
| --- | --- | --- | --- |
| Raise the heartbeat budget | May permit expensive commands to finish | Does not fix framing, rollback, cumulative accounting, or other exceptions | Not the primary repair |
| Disable heartbeat limits | Avoids this limit | Removes bounded native computation | Reject |
| Send diagnostics to stderr and exit | Preserves stdout framing | Every resource failure destroys all retained snapshots | Fatal fallback when rollback is unsafe |
| Catch only the tactic body | Small change | Misses validation, serialization, diagnostic rendering, and other commands | Reject |
| Shared transactional command boundary | Covers all response-producing phases and supports safe continued search | Requires explicit state and budget ownership | Chosen |

## Agreed wire contract

Publish protocol revision `3` with descriptor fields `resourceErrorVersion: 1`
and `commandTransactionVersion: 1`. Preserve existing model-expression,
transition, inspection, and certification versions and representations.
Revision 3 requires compact single-line JSON regardless of diagnostic content.
The maintained client and contract captures migrate together. Do not add
automatic revision-2 fallback or parse human-readable stdout as protocol data.

A heartbeat failure whose command state was successfully restored has this
shape:

```json
{
  "error": "resource",
  "desc": "Lean command heartbeat budget exhausted",
  "resource": {
    "version": 1,
    "kind": "heartbeats",
    "phase": "execute",
    "limit": 200000
  },
  "recovery": "command-rolled-back"
}
```

Define the fields precisely:

- `error` is `resource` for classified resource exhaustion and `internal` for
  an unexpected server exception.
- `desc` is bounded human-readable information. Clients never classify by it.
- `resource.version` is the resource-details schema version, initially `1`.
- `resource.kind` is initially `heartbeats`; do not advertise other kinds until
  they have typed detection and regression tests.
- `resource.phase` is one of `execute`, `validate`, `observe`, or `serialize`.
  The server tracks the phase explicitly, rather than inferring it from text.
- `resource.limit` is a positive integer in Lean's `maxHeartbeats` option units,
  which count thousands of underlying heartbeats. It is not seconds.
- `recovery` is `command-rolled-back` only if the entire failed command was
  restored and no result allocation was published. Otherwise it is
  `session-unusable`.

A classified heartbeat failure may use `session-unusable` if rollback cannot
be established. An unexpected exception uses:

```json
{
  "error": "internal",
  "desc": "Unexpected REPL command failure",
  "recovery": "session-unusable"
}
```

No error includes `stateId`, `nextStateId`, success flags, or certificate fields.
The full schema and fixtures must be identical to the companion client plan.
Existing ordinary argument/tactic errors keep their established payloads.

## Chosen architecture

Use a shared request transaction with this sequence:

1. Parse the complete input command and validate its envelope.
2. Establish a fresh finite heartbeat origin for that command.
3. Record the entry REPL state, relevant Lean state, and processing phase.
4. Execute, validate, observe, and encode the complete compact response under
   that command budget. A successful `goal.start` root or tactic result must
   not be committed before response encoding succeeds.
5. Commit the staged state and write the complete response once.
6. If execution fails before publication, restore the entry state and emit a
   bounded error response outside the exhausted execution budget.
7. If rollback or output delivery cannot be established, stop accepting input,
   report bounded diagnostics to stderr, and exit nonzero.

Stage complete response bytes before committing. A partial pipe write cannot
be rolled back; it makes the session unusable and must never be followed by a
second response for the same command. An error response is best-effort when
the output channel itself has failed.

Rollback covers the retained-state table, options, trusted environment state,
messages, and other command-visible Lean state. Preserve freshness of IDs and
never collide with a live allocation. "Rolled back" does not promise reversal
of arbitrary external IO performed by tactics. Audit commands with irreversible
effects and terminate when their session state cannot be restored safely.

## Stage 0 — Freeze evidence and the joint contract

1. Record application, client, REPL, executable, toolchain, and Mathlib identities
   from the failing deployment. Keep the two captured failure lines as evidence.
2. Add bounded request/response tracing for a controlled reproduction, including
   command name, tactic text, selected state/goal, phase, and heartbeat usage.
   Never put that trace on protocol stdout.
3. Specify the descriptor, both error variants, supported commands, and recovery
   semantics in `doc/`. Share machine-readable fixtures with the client.
4. Audit all dispatch operations, including raw-only operations such as
   `goal.continue`, `env.add`, and `frontend.process`. Commands the maintained
   client does not expose still need valid command-loop behavior.

Exit gate: a reviewed shared schema and recorded unknowns. Exact reproduction
of the original complex theorem is desirable but not a prerequisite for a
deterministic resource-boundary test.

## Stage 1 — Correct request-scoped computation budgets

1. Introduce one shared command runner. Reset Lean's heartbeat origin on entry
   with the pinned toolchain's `withCurrHeartbeats` or its verified equivalent.
   Check restored contexts so nested tactic/serialization work uses the intended
   origin instead of reinstating an old session origin.
2. Keep a finite budget covering the entire command, including diagnostics,
   validation, model serialization, transition provenance, and JSON encoding.
   Nested resets must not silently grant unbounded work to individual phases.
3. Keep final certification's explicit budget behavior consistent and documented.
   Ensure an exhausted outer budget cannot prevent returning its existing
   `inconclusive` result. Neither budget exhaustion nor recovery may create a
   certificate.
4. Use a separate small finite emergency allowance if restoring/reporting needs
   Lean computation. Prefer literal, bounded error construction in IO that does
   not invoke pretty printing or type reduction.
5. Do not add an application JSON budget setting in this repair unless needed
   for a separately reviewed requirement. Native deterministic tests may set a
   low budget through a test harness or existing native option mechanism.

Exit gate: many cheap commands continue to succeed after their combined work
exceeds one command budget; a genuinely over-budget command fails predictably.

## Stage 2 — Transactional execution and exception containment

1. Extract transaction ownership from the outer loop into a shared command runner
   used by every dispatch path. Stage state changes until response bytes exist.
2. Restore failed starts, tactics, option changes, environment changes, and
   deletion operations according to audited command semantics. Preserve the
   existing inner tactic isolation and extend protection through observation
   and serialization.
3. Track the phase explicitly. Classify heartbeat failures using pinned Lean
   exception mechanisms and the relevant budget/counter evidence. Do not rely
   only on matching `timeout` in a formatted message. If classification is
   ambiguous, use a fatal internal error rather than assert safe recovery.
4. Audit ordinary tactic exception catches. Heartbeat exhaustion must reach the
   shared classifier instead of being reduced to an untyped `tacticErrors`
   string. Preserve ordinary tactic diagnostics unchanged.
5. Avoid rendering an arbitrary `MessageData` under the already exhausted budget.
   Failure in rich diagnostic rendering must still produce the minimal bounded
   envelope or terminate without stdout contamination.
6. Add the revision-3 descriptor and error structures. Remove outer-loop plain
   stdout exception printing; unrecoverable startup/process failures go to stderr.

Exit gate: a resource failure during each protected phase produces exactly one
valid error line and leaves every preexisting handle usable when rollback is
claimed. An injected rollback failure terminates the session.

## Stage 3 — Native and framing regression tests

Extend `Test/` and a raw executable harness with:

- Actual low-heartbeat exhaustion exercising `whnf` or equivalent reduction,
  followed by a successful tactic on the same retained input.
- Repeated inexpensive commands proving that accounting is per request.
- Failures in execution, validation, observation, diagnostic rendering, and
  serialization. Use deterministic fault injection for phases that are hard to
  exhaust naturally; retain at least one genuine native-heartbeat reproduction.
- State-count and option/environment comparisons before/after rollback. A failed
  allocation must not appear in `stat`; live states keep their identities.
- Deletion failure preserving all original allocations when rollback is claimed.
- Certification exhaustion never returning `certified`, followed by successful
  inspection or another request when the session remains usable.
- Fatal internal/rollback failures returning a fatal envelope when possible,
  exiting nonzero, and accepting no further commands.
- Complete line framing, escaped multiline diagnostics, and no plain
  `Uncaught IO exception` on stdout. Add a failing/broken output-channel test.
- Existing snapshot, universe, transition, safety, model-expression and kernel
  certification regressions remaining unchanged.

Run `lake build repl` and the repository's complete native tests. Establish the
right module targets from its current `lakefile.lean`; record exact commands.
Do not count synthetic fault injection as proof of native heartbeat recovery.

Exit gate: real executable evidence includes a recoverable timeout and a
subsequent certified simple proof in the same session.

## Stage 4 — Companion delivery and deployment handoff

1. Build a new executable from the reviewed fork branch, preserving the previous
   deployment binary. Record source SHA, binary hash, toolchain, imports, and
   matching Mathlib identity.
2. Capture revision-3 startup, resource failure, rollback, continued execution,
   fatal shutdown, and final cleanup exchanges for client tests.
3. Merge/publish the REPL source first; coordinate the client and application
   dependency updates before replacing a working executable. Old clients that
   require revision 2 will reject revision 3 intentionally.
4. Update the Docker full source pin and rebuild its runtime. Native JupyterHub
   launches must point to the newly built executable. No rebuild of model weights
   is inherently required, but environment/deployment identities must be checked;
   regenerate legitimate bindings if their identity inputs changed.
5. Run the companion client/application acceptance gates. Preserve logs proving
   that timed-out work is not marked as a valid proof or certificate.

## Completion criteria

- Command resource exhaustion never contaminates protocol stdout.
- Request budgets do not accidentally accumulate across the session.
- Recovery claims are backed by complete command rollback and state tests.
- Unsafe recovery ends the session; it does not continue with uncertain state.
- The revision-3 client and both application search modes pass native recovery
  and certification checks against the rebuilt executable.
- Host tests, Docker tests, and trained JupyterHub trials are reported separately.
