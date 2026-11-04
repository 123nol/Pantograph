# Revision-3 transactional resource-error handoff

Implemented locally on `feat/transactional-resource-errors`, based on maintained
fork commit `9ecaaea242f427e534aff29314513c358b4d21ad`. The implementation is
uncommitted. `provenance.json` records hashes of the source files, test log,
executable, schema, fixtures, toolchain, and dependency manifest.

The contract and shared schema are in
[doc/transactional_resources.md](../../doc/transactional_resources.md).
`capture.json` contains 22 real executable exchanges, including startup descriptor,
execution and diagnostic-rendering exhaustion, failed start rollback, continued
execution, kernel certification, cleanup, fatal internal shutdown, kernel-budget
exhaustion without a receipt, and fatal frontend exhaustion. The harness also
checks 3,000 repeated inexpensive requests, bounded stderr tracing, a broken
stdout pipe, and rejection of an unlimited startup budget. Those repeated
requests and transport checks are summarized by the harness rather than copied
into the exchange list. Startup is asserted as `ready.` by the harness.

Host verification passed:

- `lake build repl test`
- `lake test`: 351 assertions, including all existing snapshot, universe,
  transition, model-expression, validation, frontend, and certification suites.
- `lake env python3 scripts/test_transactional_resources.py --capture pantograph_backport/transactional_resources/capture.json`
- JSON Schema validation of the shared fixtures and captured resource/internal
  envelopes, including rejection of allocation IDs on errors.
- `git diff --check`

The native phase tests stage changes to allocation ownership, options, environment
declarations, message logs, and macro freshness before actual heartbeat exhaustion.
They verify that every original allocation remains available and that staged
changes disappear. A deletion failure is tested before response encoding. Native
reduction exhaustion is also exercised through the executable, followed by a
successful tactic on the same retained input and a certified proof. A separate
512-leaf proof exhausts the explicit kernel allowance, returns `inconclusive`
without a receipt, and later certifies with the normal allowance.

Frontend observation now uses the caller's CoreM budget. All repository callers
were migrated. `goal.print` also uses snapshot isolation so printing an older
state cannot remove subsequently added environment declarations. The obsolete
`printJsonPretty` option was removed; revision 3 always uses compact lines.

State restoration is implemented by discarding separate staged state references.
There is no restoration callback to fail or require an emergency Lean allowance.
Unexpected exceptions exercise the fatal path. Error construction uses bounded
literal IO operations. Arbitrary external tactic IO cannot be undone, and native
crashes or OS termination can prevent a response. Frontend resource errors are
fatal because imports and output-file writes may have external effects.

## Remaining delivery gates

The failing deployment's application/client commits, executable hash, source
trace, tactic, Mathlib identity, and failing phase remain unknown. The only
incident evidence supplied is:

```text
Uncaught IO exception
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

These host tests import `Init` and `Test.ContractFixtures`; they do not establish
Mathlib, application, Docker, or trained JupyterHub acceptance. No failing
production theorem was reproduced. No deployed binary was edited or replaced.
The binary hash identifies a local development build from the recorded source
base plus uncommitted source hashes, not a published release commit.

Before replacing a working executable, publish the reviewed REPL source, copy
the exact schema and fixtures to the maintained client, migrate its strict
revision check to 3, and run both application search modes against the rebuilt
binary. Check environment/binding identities and the matching Mathlib pin.
Then update the Docker full source pin, rebuild and test Docker, configure native
JupyterHub launches, and record the deployment's executable hash and trained-run
logs. Preserve the existing deployment binary for rollback. The client and
application repositories and deployment configurations are outside this checkout.
Historical revision-1/revision-2 captures remain unchanged and are not proof of
revision-3 client compatibility.
