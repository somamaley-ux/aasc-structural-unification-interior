# AASC pre-5A foundation

Private, curated source baseline of the accepted common-kernel construction, its canonical licensing / Einstein–Hilbert / free scalar endpoints, native special relativity, and accepted expansion stages 1–4. Stage 5A and later working material are excluded.

The export contains 1,056 project Lean modules (including the accepted Stage 4 audit), the consumed third-party dependency sources, pinned dependency revisions, licence notices, and path-redacted acceptance evidence. Project source bytes and namespaces are preserved. This is a curated snapshot with a new history, rather than a copy of the active project's Git history.

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

## Reproduction

Pinned compiler: Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`. Pinned mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The complete dependency lock is in `lake-manifest.json` and `metadata/dependency-lock.json`.

The verified Windows replay uses an existing pinned `kr1` dependency bundle, checks the compiler and dependency object hashes, and rebuilds every project module into a new directory with no retained project objects on the search path:

```powershell
python replay.py --bundle <path-to-kr1-bundle> --out <new-output-directory> --jobs 2
```

The bundle's vendor runtime and dependency binaries are an external prerequisite for this verified mode; binaries are excluded from Git. This is a clean project-source rebuild, with pinned dependency binaries reused. It is not a clean-machine toolchain or mathlib bootstrap. `metadata/accepted-dependency-objects.json` and `metadata/accepted-dependency-companions.json` identify the exact reused objects and runtime files. Consumed dependency sources and notices are included under `vendor/` for inspection and provenance.

Run `python verify.py` to check the exported file hashes without Lean. The complete Lake configuration was also loaded successfully using separate local dependency clones at the pinned revisions; see `evidence/lake-configuration-check.json`.

For a fresh dependency installation, the standard Lake configuration is provided:

```powershell
lake update
lake exe cache get
lake build
python replay.py --lake --out <new-output-directory> --jobs 2
```

Keep the pinned revisions in the lockfile. The source-bootstrap / Lake path has not been established by the historical acceptance or by this export's retained-binary replay. It may require network access and package setup. No cross-platform build claim is made.

`replay.py` writes per-module logs, object hashes, a result receipt and `endpoint-audit.log`. The final audit checks the six named roots and reports their axioms. The accepted roots use the standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice`; a new replay must report its actual results.

An interrupted replay can use the same command with `--resume`. It verifies the source-manifest identity, compiler, recorded object hashes, compile-log hashes and completed dependency graph before continuing. The export verification used one such checkpoint within its clean output directory; the receipt distinguishes those fresh objects from the later resumed compilation. No project objects were copied from the active or historical build trees.

## Provenance and rights

`metadata/project.json` records exact source hashes, imports, original accepted object hashes, and source provenance. `SOURCE` in evidence is a portable placeholder for the original workspace prefix. Redacted evidence records its original SHA-256; it is a transformed copy and cannot itself match that original hash. Historical instructions and publication status in those records describe their original acceptance, not this export's authorization.

Only the accepted import closure, scope evidence and dependency notices were selected. The active project, private conversation logs, credentials, raw corpus archives, PDF/manuscript collections, build caches, failed attempts, and 5A work are excluded. Source comments and dependency headers remain intact.

Original project material remains private; this export assigns no new public licence to it. Third-party material retains its own licence and copyright notices under each `vendor/packages/*/source` directory. Lean's notices are under `vendor/toolchain`. The dependency lock records upstream origins and revisions. No third-party runtime binaries are redistributed in this repository.

## Export verification result

All 1,056 project modules rebuilt successfully in the isolated clean replay, and every resulting object matched its accepted SHA-256. The six named endpoint axiom reports contain exactly `propext`, `Quot.sound`, and `Classical.choice`. Full module receipts, compile logs, the checkpoint and endpoint audit are under `evidence/clean-replay/`.

1,054 project source hashes are directly listed in the accepted source ledgers or seal file maps checked for this export. Two early Stage 1 source files (`EHKGCurvedOperand` and `EHKGCurvatureWitness`) are instead verified through fresh compilation to their exact accepted object hashes. `evidence/accepted-source-hash-check.json` records that distinction.
