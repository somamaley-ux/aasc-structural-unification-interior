"""Rebuild the publication modules from source and check the joint import.

Use an empty output directory. The native 4.28 project and pinned dependency
imports should already have been compiled; see README.md for the Lake route.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--native-project", type=Path, required=True)
parser.add_argument("--lean-bin", type=Path, required=True)
parser.add_argument("--out", type=Path, required=True)
parser.add_argument("--resume", action="store_true", help="Resume only hash-verified successful steps from this same output directory")
parser.add_argument("--jobs", type=int, default=2)
parser.add_argument("--mathlib-overlay", type=Path, help="Optional compiled mathlib search root including OfNorm")
args = parser.parse_args()
here = Path(__file__).resolve().parent
repo = here.parent
out = args.out.resolve()
out.mkdir(parents=True, exist_ok=args.resume)
native = args.native_project.resolve()
lean_bin = args.lean_bin.resolve()
suffix = ".exe" if os.name == "nt" else ""
compiler = lean_bin / ("lean" + suffix)
checker = lean_bin / ("leanchecker" + suffix)
path_parts = [out, native / ".lake/build/lib/lean"]
if args.mathlib_overlay:
    path_parts.append(args.mathlib_overlay.resolve())
packages = native / ".lake/packages"
path_parts += [p / ".lake/build/lib/lean" for p in sorted(packages.iterdir())
               if p.is_dir() and (p / ".lake/build/lib/lean").is_dir()]
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(map(str, path_parts))
env["PATH"] = str(lean_bin) + os.pathsep + env["PATH"]
def run(command):
    p = subprocess.run(list(map(str, command)), cwd=out, env=env, capture_output=True)
    log = (p.stdout+p.stderr).decode("utf-8", errors="replace")
    if p.returncode:
        raise RuntimeError(f"Failed {command[-1]} ({p.returncode})\n{log}")
    return log.strip()
version = run([compiler, "--version"])
assert "version 4.28.0," in version, version
expected_lock = json.loads((repo / "lake-manifest.json").read_text(encoding="utf8"))
provided_lock = json.loads((native / "lake-manifest.json").read_text(encoding="utf8"))
def locked_revisions(lock):
    return {row["name"]:row["rev"] for row in lock["packages"]}
if locked_revisions(expected_lock) != locked_revisions(provided_lock):
    raise ValueError("Supplied native workspace has different dependency revisions.")
native_inventory = json.loads((repo / "metadata/project.json").read_text(encoding="utf8"))
for row in native_inventory:
    native_source = native / row["source"]
    if hashlib.sha256(native_source.read_bytes()).hexdigest() != row["sha256"]:
        raise ValueError(f"Native source differs from the publication baseline: {row['source']}")
sources = {file.stem: file for file in here.glob("*.lean")}
sources.pop("PreparationPublicationAudit", None)
sources["KernelFaithfulOperationalSR"] = repo / "src/KernelFaithfulOperationalSR.lean"
sources["ProjectionCoverage"] = repo / "audit/ProjectionCoverage.lean"
# This supplement uses standard mathlib. A partial dependency cache can be
# completed by Lake in the native workspace, or supplied via --mathlib-overlay.
if "TravelTimePolarization" in sources:
    for name in ["Mathlib.Algebra.Module.LinearMap.Rat",
                 "Mathlib.Analysis.InnerProductSpace.OfNorm"]:
        rel = Path(*name.split("."))
        if all(not (p / rel.with_suffix(".olean")).is_file() for p in path_parts):
            raise SystemExit(f"Missing mathlib dependency {name}. Build +{name} in the pinned workspace or pass --mathlib-overlay.")
raw = {name:p.read_bytes() for name,p in sources.items()}
deps = {name: set(re.findall(r"^(?:public |private )?import\s+([\w.]+)",
                             data.decode("utf-8-sig"),flags=re.M)) & sources.keys()
        for name,data in raw.items()}
pending = set(sources)
completed = {}
step_file = out / "compile-steps.json"
saved = json.loads(step_file.read_text(encoding="utf8")) if args.resume else {}
file_sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
def reuse_step(name):
    row = saved.get(name, {})
    base = out / Path(*name.split("."))
    local_source = base.with_suffix(".lean")
    obj = base.with_suffix(".olean")
    return (local_source.is_file() and obj.is_file() and
            row.get("source_sha256") == hashlib.sha256(raw[name]).hexdigest() ==
            file_sha(local_source) and row.get("object_sha256") == file_sha(obj) and
            all(completed[d].get("resumed") for d in deps[name]))
def save_steps():
    temp = step_file.with_suffix(".tmp")
    temp.write_text(json.dumps(saved,indent=2)+"\n",encoding="utf8")
    temp.replace(step_file)
def compile_one(name):
    path = Path(*name.split("."))
    src = out / path.with_suffix(".lean")
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_bytes(raw[name])
    began = time.monotonic()
    strict = [] if name == "KernelFaithfulOperationalSR" else ["-DwarningAsError=true"]
    log = run([compiler, *strict, "-o", path.with_suffix(".olean"),
               path.with_suffix(".lean")])
    if log:
        (out / (name + ".log")).write_text(log+"\n",encoding="utf8")
    return {"sha256":hashlib.sha256(raw[name]).hexdigest(),
            "object_sha256":file_sha(out / path.with_suffix(".olean")),
            "compile_seconds":round(time.monotonic()-began,2)}
if not 1 <= args.jobs <= 4: raise ValueError("Use one to four concurrent compilers")
with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
    running = {}
    while pending or running:
        for name in sorted(pending):
            if len(running) >= args.jobs: break
            if deps[name] <= completed.keys():
                pending.remove(name)
                if reuse_step(name):
                    row = saved[name]
                    completed[name] = {"sha256":row["source_sha256"],"source_sha256":row["source_sha256"],"object_sha256":row["object_sha256"],
                                       "resumed":True}
                    continue
                running[pool.submit(compile_one,name)] = name
        if not running:
            if pending and not any(deps[n] <= completed.keys() for n in pending):
                raise ValueError("Circular imports: "+str(pending))
            continue
        done,_ = concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for future in done:
            name = running.pop(future)
            completed[name] = future.result()
            completed[name]["source_sha256"] = completed[name]["sha256"]
            saved[name] = {"source_sha256":completed[name]["sha256"],"object_sha256":completed[name]["object_sha256"]}
            save_steps()
            print("Compiled",name,flush=True)
receipt = {"lean":version,"fresh_objects":completed,
           "hash_fields":{"sha256":"source bytes, identical to source_sha256","object_sha256":"compiled .olean bytes"},
           "checked_native_source_hashes":len(native_inventory),
           "reused":"Prebuilt pinned native project dependencies and mathlib",
           "warnings_as_errors":"All publication sources. The unmodified native Stage 4 root uses its original warnings policy."}
def audit_publication():
    checks = ["PreparationPublication", "TravelTimePolarization", "TransitiveRestRotations","NativeTransitiveRestFrame",
              "OccupiedSmoothMetricResponse", "FourDimensionalMetricResponse",
              "FourDimensionalDiv2", "SmoothMetricResponse"]
    receipt["kernel_replay"] = {m:run([checker,"-v",m]) for m in checks}
    audit = here / "PreparationPublicationAudit.lean"
    audit_copy = out / audit.name
    shutil.copyfile(audit, audit_copy)
    raw_audit = run([compiler,"-DwarningAsError=true",audit.name])
    (out / "audit.log").write_text(raw_audit+"\n", encoding="utf8")
    axioms = {n:[x.strip() for x in xs.split(",") if x.strip()]
              for n,xs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw_audit)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",raw_audit): axioms[n]=[]
    declared = set(re.findall(r"^#print axioms ([\w.]+)",audit.read_text(encoding="utf8"),flags=re.M))
    allowed = {"Classical.choice","Quot.sound","propext"}
    if axioms.keys()!=declared or any(set(a)-allowed for a in axioms.values()):
        raise ValueError("Axiom inventory differed from declarations. See audit.log.")
    receipt["audited_axioms"] = axioms
audit_publication()
(out / "verification.json").write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf8")
print("PASSED",len(completed),"fresh compilations",flush=True)
