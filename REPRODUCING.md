# Build and reproduction

The verified cache-cold route compiled all **1,056 project modules** and **3,404 consumed dependency modules** from source on 31 October 2026. It used fresh official Lean 4.28.0 binaries on the existing Windows host, rather than an installed Lean toolchain or pre-existing dependency cache. It did not provision a clean OS/VM or rebuild the compiler/bundled standard library from C++/stage0. Existing Windows, Git, Python and certificate-store prerequisites remained.

[The report](evidence/cache-cold-bootstrap/report.json), [portable acquisition commands](evidence/cache-cold-bootstrap/acquisition-commands.json), [command journal](evidence/cache-cold-bootstrap/commands.jsonl) and [source-build log](evidence/cache-cold-bootstrap/source-build.log) record the executed check. The commands below present that procedure with user-selected paths; they are not a claim that another OS or every shell has been tested.

## 1. Check source identity and pins

Use a fresh checkout of this repository and Python 3.10+:

```powershell
git clone https://github.com/somamaley-ux/aasc-structural-unification-interior.git
Set-Location aasc-structural-unification-interior
python verify.py
```

The tested mathematical source snapshot was commit `6ac8f9e8c6f1ead60dc1057924058991399d8b94`. The subsequent publication edits preserve all production Lean source bytes and pinned dependencies. The export hash manifest includes current documentation and evidence as well as sources; `verify.py` is an integrity check and does not invoke Lean.

`lean-toolchain` pins Lean 4.28.0. `lake-manifest.json` and `metadata/dependency-lock.json` pin all nine dependency revisions, including mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Keep these revisions; do not run an unreviewed `lake update` and treat a changed dependency set as the same check.

## 2. Acquire the fresh tools

The tested Windows archives were:

| Tool | Designated source | Verified archive SHA-256 |
| --- | --- | --- |
| Lean 4.28.0 | [Official Windows release](https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-windows.zip) | `faa0a8213ec81035d1ff3745d6d28e55b9d80de63fb9cd33380cd51b23cfc1aa` |
| Node 24.22.2, npm 11.19.1 | [Official Windows archive](https://nodejs.org/dist/v24.22.2/node-v24.22.2-win-x64.zip), [official checksums](https://nodejs.org/dist/v24.22.2/SHASUMS256.txt) | `ca1bff5d8ead13c9f2ea404a176db46bd430704d5b5113734049fa365e7799e2` |

Verify downloaded archives with `Get-FileHash -Algorithm SHA256` and extract into new directories. The compiler reports commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`; the tested `lean.exe` SHA-256 is `6a66c4a5739fa17146b88ac81bab2bca1924806cac321ddad6b96006dde9c691`. Node major 24 follows the pinned ProofWidgets build workflow. Neither tool is installed globally by this procedure.

## 3. Isolate the process environment

Open a dedicated PowerShell process. Set the following paths to the newly extracted tools and a new empty directory outside the checkout. Set `$taskGitBin` to the directory containing the selected Git executable. Preserve the full path to the selected Python interpreter if it will be used after replacing `PATH`.

```powershell
$taskRepo = (Get-Location).Path
$taskLeanBin = '<new Lean extraction>/bin'
$taskNodeHome = '<new Node extraction>'
$taskGitBin = '<Git executable directory>'
$taskHome = '<new empty bootstrap directory>'
if (Test-Path -LiteralPath $taskHome) { throw 'Use a new empty bootstrap directory' }
New-Item -ItemType Directory -Path $taskHome | Out-Null
Get-ChildItem Env: | Where-Object Name -Match '^(LEAN_|LAKE_|ELAN_|MATHLIB_)' |
  ForEach-Object { Remove-Item -LiteralPath "Env:$($_.Name)" }
Remove-Item Env:NODE_PATH,Env:NODE_OPTIONS -ErrorAction SilentlyContinue
$env:PATH = "$taskLeanBin;$taskNodeHome;$taskGitBin;C:\Windows\System32;C:\Windows\System32\WindowsPowerShell\v1.0;C:\Windows"
$env:ELAN_HOME = Join-Path $taskHome 'elan'
$env:LAKE_HOME = Join-Path $taskHome 'lake'
$env:XDG_CACHE_HOME = Join-Path $taskHome 'xdg-cache'
$env:MATHLIB_CACHE_DIR = Join-Path $taskHome 'mathlib-cache'
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
$env:LEAN_NUM_THREADS = '4'
$env:GIT_CONFIG_NOSYSTEM = '1'
$env:GIT_CONFIG_GLOBAL = Join-Path $taskHome 'empty.gitconfig'
$env:GIT_TERMINAL_PROMPT = '0'
$env:NPM_CONFIG_CACHE = Join-Path $taskHome 'npm-cache'
$env:NPM_CONFIG_USERCONFIG = Join-Path $taskHome 'npm-user.npmrc'
$env:NPM_CONFIG_GLOBALCONFIG = Join-Path $taskHome 'npm-global.npmrc'
New-Item -ItemType File -Path $env:GIT_CONFIG_GLOBAL,$env:NPM_CONFIG_USERCONFIG,$env:NPM_CONFIG_GLOBALCONFIG | Out-Null
lean --version
node --version
npm.cmd --version
```

This changes only the dedicated process environment. In the executed check, compiler lookup, prefix and every Lean library search root resolved within the new bootstrap tree. Initially there were zero project or dependency `.olean` files and zero mathlib cache files.

## 4. Fetch exact dependency sources

The executed check fetched directly from each lockfile URL/revision into a new repository, without shared Git object alternates or historical dependency clones. From the project root:

```powershell
$taskLock = Get-Content -Raw -LiteralPath '.\lake-manifest.json' | ConvertFrom-Json
foreach ($taskPackage in $taskLock.packages) {
  $taskTarget = Join-Path $taskRepo ".lake/packages/$($taskPackage.name)"
  if (Test-Path -LiteralPath $taskTarget) { throw "Dependency directory already exists: $taskTarget" }
  git init --quiet $taskTarget
  if ($LASTEXITCODE) { throw 'git init failed' }
  git -C $taskTarget remote add origin $taskPackage.url
  if ($LASTEXITCODE) { throw 'remote setup failed' }
  git -C $taskTarget fetch --depth 1 --no-tags origin $taskPackage.rev
  if ($LASTEXITCODE) { throw 'exact dependency fetch failed' }
  git -C $taskTarget checkout --quiet --detach FETCH_HEAD
  if ($LASTEXITCODE) { throw 'dependency checkout failed' }
  $taskHead = git -C $taskTarget rev-parse HEAD
  if ($taskHead -ne $taskPackage.rev) { throw 'Dependency revision mismatch' }
}
```

All nine exact HEADs and clean tracked source states were checked in the executed run. Cli was fetched because it is locked, but required no compiled library object in this build. The vendored source subsets under `vendor/` are inspection/provenance material; the Lake build uses the full pinned upstream checkouts.

## 5. Build ProofWidgets assets before the main source build

The first strict source attempt encountered mathlib's upstream ProofWidgets cache guard. Fetching precompiled Lean caches was not used to resolve it. Instead, the unchanged pinned ProofWidgets package built its own JavaScript assets as a standalone package:

```powershell
# Required on the tested host for npm's certificate chain; verification stays enabled.
$env:NODE_OPTIONS = '--use-system-ca'
$taskWidgets = Join-Path $taskRepo '.lake/packages/proofwidgets'
lake --no-cache --reconfigure -d $taskWidgets build widgetJsAll
if ($LASTEXITCODE) { throw 'ProofWidgets asset build failed' }
```

The first npm attempt failed with `UNABLE_TO_VERIFY_LEAF_SIGNATURE`. Node's system-CA option resolved that host-specific issue; a separate HTTPS check reported an authorized certificate. No TLS verification bypass or global certificate-setting change was used. `package.json`, `package-lock.json` and all pinned tracked dependency sources remained unchanged. The JavaScript build acquired npm dependencies into the new dedicated cache; this is not a claim that Node/npm tooling was itself source-bootstrapped.

## 6. Compile and audit

```powershell
lake --no-cache build Pre5A
if ($LASTEXITCODE) { throw 'Lean source build failed' }
```

Do not run `lake exe cache get` when reproducing this cache-cold source check. A cache-assisted build is a different verification mode. The successful run completed 4,476 Lake jobs, producing 1,056 project and 3,404 consumed dependency primary objects. Its mathlib binary-cache directory remained empty.

The first attempt's confirmed widget-guard failure was preserved and its remaining independent jobs stopped. The continuation reused only the 837 dependency objects newly source-built during this same check; no older dependency or project binaries were imported. “Cache-cold” describes the initial state, not a claim that every job was executed twice after the prerequisite repair.

For the retained endpoint audit, save a file outside the source tree containing:

```lean
import KernelFaithfulOperationalSR
#check AASCKleinGordon.CanonicalLicensing.kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger
#print axioms AASCKleinGordon.CanonicalLicensing.kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger
#print axioms AASCKleinGordon.CanonicalLicensing.SRIntegration.kernel_faithful_native_sr_canonical_licensing_eh_scalar
#print axioms AASCKleinGordon.CurvedKG.kernel_faithful_same_eh_curved_kg_complete
#print axioms AASCKleinGordon.SameActionSource.kernel_faithful_same_action_kg_source
#print axioms AASCKleinGordon.RecoveryComparison.kernel_faithful_recovery_comparison
#print axioms AASCKleinGordon.OperationalSR.kernel_faithful_operational_sr
```

Run `lake --no-cache env lean <path-to-audit-file>`. The executed [six-root audit](evidence/cache-cold-bootstrap/endpoint-audit.log) checked all six names and reported exactly `propext`, `Classical.choice`, and `Quot.sound` for each, with no `sorryAx`. This supplements successful compilation; the exact theorem statements remain the physics scope authority.

## Object identity and the separate historical replay

The fresh Lake build's **0/1,056** primary objects matched the accepted historical direct-build SHA-256 values. A diagnostic direct invocation for `AlgebraicCurvatureCoordinates`, using the fresh compiler and dependencies, matched its accepted hash exactly; Lake's output for the same source differed. This supports an invocation-related distinction for that sample. It does not establish a complete cause analysis or full project byte-identical reproducibility. [The diagnostic receipt](evidence/cache-cold-bootstrap/artifact-investigation.json) records the precise scope.

The earlier retained-binary export replay is separately established: all 1,056 project sources rebuilt and all 1,056 accepted primary hashes matched. To repeat that historical mode, an external pinned `kr1`-style binary bundle is required:

```powershell
python replay.py --bundle <path-to-pinned-bundle> --out <new-output-directory> --jobs 2
```

The binary bundle is absent from Git and is not required for the verified source-build route above. `replay.py --lake --out <new-output-directory> --jobs 2` provides a separate full direct project replay against installed Lake dependencies; that entire route was not executed in the later bootstrap check. Each replay must report its actual hash-match count. A valid `--resume` uses only the checkpoint it verifies, and a source/dependency/toolchain change requires a new verification boundary.

No clean-OS, cross-platform, compiler-stage0, unrestricted physics or unresolved complete object-hash claim is implied by these instructions.
