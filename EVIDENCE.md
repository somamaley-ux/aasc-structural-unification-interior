# Reading the evidence

The production entry point is [KernelFaithfulOperationalSR.lean](src/KernelFaithfulOperationalSR.lean). The six named roots and their construction boundaries are in [README.md](README.md) and [CONSTRUCTION.md](CONSTRUCTION.md). [The accepted inventory](evidence/accepted-endpoint-inventory.json) is a transformed historical record, not the current permission or verification authority.

## Three verification layers

1. **Stage acceptance.** The connected composition, native SR and stages 1–4 have scoped acceptance/review records below. These bind their own source/objects, hypotheses and reuse boundaries. Their original “private,” “pending,” “next stage,” and publication/replay instructions remain historical. Later accepted stages supersede earlier stage-local remaining-work lists only where the later exact statements do so.
2. **Full export replay.** [The result](evidence/clean-replay/result.json), [checkpoint](evidence/clean-replay/checkpoint.json), per-module logs and [six-root audit](evidence/clean-replay/endpoint-audit.log) record all 1,056 project modules freshly rebuilt against rehashed retained compiler/library binaries, with all accepted primary object hashes matched. The checkpoint is intermediate; the final result establishes completion. This layer did not bootstrap the compiler or dependencies.
3. **Later cache-cold source bootstrap.** [The report](evidence/cache-cold-bootstrap/report.json), [command journal](evidence/cache-cold-bootstrap/commands.jsonl), [successful source log](evidence/cache-cold-bootstrap/source-build.log) and [six-root audit](evidence/cache-cold-bootstrap/endpoint-audit.log) record the separate 31 October 2026 check. The check began with no compiled project/dependency objects, used a fresh official toolchain and direct exact-revision upstream checkouts, source-built consumed dependencies and the project, and passed the six endpoint audits. ProofWidgets/Node/TLS prerequisites and the first failed attempt are distinguished explicitly. This layer establishes neither a new-OS/VM test nor full Lake object-hash identity.

The bootstrap evidence has portable path substitutions; [its provenance index](evidence/cache-cold-bootstrap/provenance.json) retains original file hashes and the transformation description. A transformed file cannot itself equal its original-file hash. The tested commit was `6ac8f9e8c6f1ead60dc1057924058991399d8b94`, before the documentation update and repository rename. Production Lean bytes and dependency pins are preserved, so the later documentation commit does not silently claim a new proof build.

## Historical scope records

| Layer | Evidence |
| --- | --- |
| Common Kernel / canonical licensing / EH / free scalar | [Composition scope](evidence/connected-canonical-licensing-20261019/COMPOSITION_SCOPE.md), [independent review](evidence/connected-canonical-licensing-20261019/STAGE4_CONNECTED_REVIEW.json), [acceptance](evidence/connected-canonical-licensing-20261019/accepted.json) |
| Native SR | [Scope](evidence/sr-full-integration-20261019/SCOPE.md), [independent review](evidence/sr-full-integration-20261019/INDEPENDENT_REVIEW.json), [acceptance](evidence/sr-full-integration-20261019/accepted.json) |
| Stage 1 | [Mathematics and receiving scope](evidence/stage-01-curved-kg/STAGE01_MATHEMATICS_AND_SCOPE.md), [completion proof map](evidence/stage-01-curved-kg/STAGE01_COMPLETION_PROOF_MAP.json), [acceptance](evidence/stage-01-curved-kg/accepted.json). The [first geometry note](evidence/stage-01-curved-kg/GEOMETRY_CONSTRUCTION_SCOPE.md) describes an early helper, not the final stage. |
| Stage 2 | [Proof map](evidence/stage-02-same-action-source/IMPLEMENTED_PROOF_MAP.json), [final review](evidence/stage-02-same-action-source/INDEPENDENT_REVIEW_FINAL.json), [acceptance](evidence/stage-02-same-action-source/accepted.json) |
| Stage 3 | [Proof map](evidence/stage-03-recovery-comparison/IMPLEMENTED_PROOF_MAP.json), [final review](evidence/stage-03-recovery-comparison/INDEPENDENT_REVIEW_FINAL.json), [acceptance](evidence/stage-03-recovery-comparison/accepted.json) |
| Stage 4 | [Exact statement summary](evidence/stage-04-operational-sr/STAGE04_SUBSTANTIVE_SUMMARY.json), [final review](evidence/stage-04-operational-sr/FINAL_INDEPENDENT_REVIEW_001.json), [acceptance](evidence/stage-04-operational-sr/accepted.json) |

`SOURCE` replaces the original private workspace prefix in older evidence. The original acceptance source-identity limitation remains: 1,054 source hashes occur directly in checked ledgers, while `EHKGCurvedOperand` and `EHKGCurvatureWitness` were tied through exact accepted object identity in the historical full replay. See [the receipt](evidence/accepted-source-hash-check.json).

Production comments are retained verbatim as part of the source identity. Some discuss module-local or then-pending audit obligations; the final receipts above govern present completion status. Vendor comments/notices are upstream material, preserved with their licenses. This evidence index does not extend a mathematical acceptance into a larger physics claim or an assertion of independent review of unused corpus material.
