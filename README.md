# Premetric Structural Unification

## The Constraint-Governed Emergence of Geometry, Scalar Dynamics and Operational Relativity

*An Integrated Cross-Corpus Lean Formalization*

This repository contains a **machine-checked, constraint-first construction of a controlled physical interior from the AASC Kernel and downstream Kernel-faithful machinery**. Geometric Einstein response, free scalar quantum dynamics, a controlled nonflat Klein–Gordon construction, same-action classical scalar sources, quantitative recovery and operational special relativity are connected through actual source, licensing, observation and continuation maps.

The common Kernel governs standing reference, admissibility and failure. Concrete downstream constructions realize the physical carriers, geometry, dynamics and apparatus within that governance. Their physical inputs are **Kernel-governed resources**: preparations, admitted metric operands, comparisons, calibrated clocks, signal energies, use windows and protocol domains participate in explicit source/use contracts, with proved faithful descriptions and operations. The root theorems construct the endpoints and licensing conclusions; desired Einstein or Schrödinger laws, apparatus existence and compatibility certificates are not root premises.

This emergence is substantive and scoped. Continuum carriers, dimension, the KG/free branch, actions and physical parameters are declared construction choices; the realization and preservation results are proved within that branch. Kernel necessity alone does not select those choices or their numerical values. [CONSTRUCTION.md](CONSTRUCTION.md) distinguishes construction, received data, calibration and conditional conclusions without detaching the physical resources from Kernel governance.

The completed **pre-5A foundation** contains **1,056 project Lean modules**, including accepted stages 1–4 and the final Stage 4 audit, consumed third-party dependency sources/notices, pinned revisions and path-redacted acceptance evidence. Production source bytes and namespaces are preserved. This curated snapshot has its own history. Later working branches and manuscript/PDF collections are excluded; this repository publication creates no paper publication, GitHub release or Zenodo deposit.

## Accepted endpoints and scope

| Endpoint | Construction and limits |
| --- | --- |
| `CanonicalLicensing.kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger` | Common-kernel canonical licensing to the declared admitted EH/Einstein response and constructed free Schrödinger receiving sector. The accepted bounded common-kernel capstone. |
| `CanonicalLicensing.SRIntegration.kernel_faithful_native_sr_canonical_licensing_eh_scalar` | Native SR geometry and clocks with the same-source canonical licensing / EH / scalar integration. |
| `CurvedKG.kernel_faithful_same_eh_curved_kg_complete` | Stage 1: controlled nonflat same-admitted-EH-metric real KG Cauchy construction and action / use / continuation connections. |
| `SameActionSource.kernel_faithful_same_action_kg_source` | Stage 2: same-action scalar stress, Ward / exchange / Hamiltonian results, and conditional sourced Einstein receiving. |
| `RecoveryComparison.kernel_faithful_recovery_comparison` | Stage 3: quantitative flat nonrelativistic recovery and controlled local metric / field / guarded-duration comparisons. |
| `OperationalSR.kernel_faithful_operational_sr` | Stage 4: continuous coasting clocks and occupied finite radar / ruler / network protocols, retaining the preceding endpoints. |

All names above have prefix `AASCKleinGordon.`. The root source is `src/KernelFaithfulOperationalSR.lean`; its 229 fields comprise 227 named receipts and two retained whole endpoints. That field count is not a count of independent physical theorems.

The root takes positive mass, speed and hbar in `Parameters`, real `s`, `kappa`, `Lambda`, and nonzero `kappa`. Actual branch domain, preparation, calibration, interval, resource and comparison hypotheses remain in their stated theorems. The EH branch has its declared response/classification envelope. The quantum branch is the constructed free isolated scalar sector with its exact domains; the curved KG branch uses the controlled metric class. The sourced Einstein result is conditional on the stated combined-action stationarity. This baseline does not establish arbitrary curved KG evolution, global coupled Einstein–KG existence, general interacting quantum theory, quantum gravity, arbitrary accelerating apparatus, or the Standard Model extension.

The older `evidence/older-interface/CapstoneObligations.lean` is retained explicitly as a certificate-to-conjunction interface receiving six obligations. It is outside the replayed production sources. Its presence does not certify the wider paper-level Unus / Gravity / A–D chain. See `evidence/accepted-endpoint-inventory.json` and the accepted scope reviews for the exact distinction.

## Reproduction and verification

Pinned compiler: **Lean 4.28.0**, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`. Pinned mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Complete revisions are in [lake-manifest.json](lake-manifest.json) and [metadata/dependency-lock.json](metadata/dependency-lock.json).

```powershell
python verify.py
```

This checks the exported files without Lean. [REPRODUCING.md](REPRODUCING.md) gives the pinned source-build procedure, including the required standalone ProofWidgets asset build, and explains the separate retained-binary replay.

| Verification | Actual result and boundary |
| --- | --- |
| [Historical export replay](evidence/clean-replay/result.json) | All 1,056 project modules freshly rebuilt; all 1,056 primary objects matched accepted hashes. Existing pinned compiler and dependency binaries were rehashed and reused. |
| [Cache-cold source bootstrap, 31 October 2026](evidence/cache-cold-bootstrap/report.json) | Fresh official Lean binaries and exact upstream dependency checkouts, starting with zero project/dependency objects. All 1,056 project and 3,404 consumed dependency modules compiled from source; all six endpoint audits passed. Existing Windows host, with no new OS/VM, compiler stage0 bootstrap or cross-platform verification. |

Both endpoint audits report exactly `propext`, `Quot.sound`, and `Classical.choice` for each of the six named roots. These are foundational axiom reports, not a removal of the quantified mathematical or physical hypotheses.

**Full Lake object-hash identity remains unresolved.** None of the 1,056 fresh Lake-produced primary objects matched the historical direct-build hashes. One diagnostic historical direct invocation, using the fresh dependencies, reproduced its accepted object exactly. A successful cache-cold source build is established; complete byte-for-byte reproduction by that fresh route is not. No complete second direct replay is implied.

The source build required ProofWidgets `widgetJsAll` to be built separately using fresh Node 24 and its unchanged pinned package-lock. On the tested host, `NODE_OPTIONS=--use-system-ca` resolved npm's certificate-chain error with TLS verification enabled. The initial failed attempt and continuation using only outputs newly compiled during this check are recorded explicitly. [EVIDENCE.md](EVIDENCE.md) separates these facts from earlier acceptance and replay results.

## Provenance and rights

`metadata/project.json` records exact source hashes, imports, original accepted object hashes, and source provenance. `SOURCE` in evidence is a portable placeholder for the original workspace prefix. Redacted evidence records its original SHA-256; it is a transformed copy and cannot itself match that original hash. Historical instructions and publication status in those records describe their original acceptance, not this export's authorization.

Only the accepted import closure, scope evidence and dependency notices were selected. The active project, private conversation logs, credentials, raw corpus archives, PDF/manuscript collections, build caches, unrelated working trees, and 5A work are excluded. Source comments and dependency headers remain intact.

Original project material is provided for inspection without a new project-wide licence grant. See [RIGHTS.md](RIGHTS.md) for the existing rights position. Third-party material retains its own licence and copyright notices under each `vendor/packages/*/source` directory. Lean's notices are under `vendor/toolchain`. The dependency lock records upstream origins and revisions. No third-party runtime binaries are redistributed in this repository.

## Historical export verification result

In the retained-binary export replay, all 1,056 project modules rebuilt successfully in the isolated output, and every resulting object matched its accepted SHA-256. The six named endpoint axiom reports contain exactly `propext`, `Quot.sound`, and `Classical.choice`. Full module receipts, compile logs, the checkpoint and endpoint audit are under `evidence/clean-replay/`.

1,054 project source hashes are directly listed in the accepted source ledgers or seal file maps checked for this export. Two early Stage 1 source files (`EHKGCurvedOperand` and `EHKGCurvatureWitness`) are instead verified through fresh compilation to their exact accepted object hashes. `evidence/accepted-source-hash-check.json` records that distinction.

Historical stage notes and receipts retain their original dates and verification boundaries. Their words “private,” “pending,” and “next stage” describe the stage at that time; [EVIDENCE.md](EVIDENCE.md) supplies the current reading context.
