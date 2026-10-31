"""Rebuild all curated project sources using pinned, verified library binaries.

Python 3.10+. --bundle points to an existing kr1-style pinned vendor directory's
parent; only vendor binaries are reused. --lake uses this checkout's Lake deps.
Creates a new output directory, or resumes its verified checkpoint. Never imports
project objects from outside that clean rebuild directory.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,time
ROOT=Path(__file__).resolve().parent
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v): p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
def main():
 ap=argparse.ArgumentParser(); group=ap.add_mutually_exclusive_group(required=True)
 group.add_argument('--bundle',type=Path); group.add_argument('--lake',action='store_true')
 ap.add_argument('--out',required=True,type=Path); ap.add_argument('--jobs',type=int,default=2)
 ap.add_argument('--resume',action='store_true')
 args=ap.parse_args(); out=args.out.resolve(); assert out.exists()==args.resume,'Output must be new, unless resuming'; assert 1<=args.jobs<=8
 meta=read(ROOT/'metadata/dependencies.json'); rows=read(ROOT/'metadata/project.json'); sources={r['module']:r for r in rows}
 for row in rows: assert sha(ROOT/row['source'])==row['sha256'],row['module']
 env=os.environ.copy()
 for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE','LAKE_HOME','ELAN_TOOLCHAIN']: env.pop(k,None)
 if args.bundle:
  bundle=args.bundle.resolve(); lean=bundle/meta['lean']; assert sha(lean)==meta['lean_sha256'],'Compiler hash mismatch'
  libs=[bundle/r['root'] for r in meta['library_roots'] if not r.get('retained_path_missing')]
  for r in read(ROOT/'metadata/accepted-dependency-objects.json'): assert sha(bundle/r['object'])==r['sha256'],r['module']
  for r in read(ROOT/'metadata/accepted-dependency-companions.json'): assert sha(bundle/r['path'])==r['sha256'],r['path']
  mode='All project sources rebuilt; retained dependency binaries rehashed and reused'
 else:
  cmd=subprocess.run(['lake','env','lean','--print-prefix'],cwd=ROOT,capture_output=True,text=True,check=True)
  lean=Path(cmd.stdout.strip())/'bin'/('lean.exe' if os.name=='nt' else 'lean')
  libs=[ROOT/'.lake/packages'/r['name']/'.lake/build/lib/lean' for r in read(ROOT/'lake-manifest.json')['packages']]
  mode='All project sources rebuilt against Lake-managed dependencies; source bootstrap not certified by original acceptance'
 version=subprocess.run([str(lean),'--version'],env=env,capture_output=True,text=True,check=True).stdout.strip()
 assert '4.28.0' in version and '7e01a1bf5c70' in version,version
 lib=Path(subprocess.run([str(lean),'--print-libdir'],env=env,capture_output=True,text=True,check=True).stdout.strip())
 if args.bundle: assert lib.resolve().is_relative_to((bundle/'vendor/toolchain').resolve()),'Compiler library directory escaped pinned bundle'
 libs.append(lib); out.mkdir(parents=True,exist_ok=args.resume); build=out/'build'; build.mkdir(exist_ok=args.resume); logs=out/'logs'; logs.mkdir(exist_ok=args.resume)
 env['LEAN_PATH']=os.pathsep.join(map(str,[build]+libs)); env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 for r in rows: (build/Path(r['module'].replace('.','/'))).parent.mkdir(parents=True,exist_ok=True)
 pending=set(sources); done=set(); running={}; receipts=[]; start=time.time(); prior_elapsed=0
 if args.resume:
  checkpoint=read(out/'checkpoint.json'); assert checkpoint['project_manifest_sha256']==sha(ROOT/'metadata/project.json')
  assert checkpoint['compiler_sha256']==sha(lean); prior_elapsed=checkpoint.get('prior_elapsed_seconds',0)
  receipts=[json.loads(line) for line in (out/'receipts.jsonl').read_text(encoding='utf-8').splitlines() if line]
  for r in receipts:
   m=r['module']; assert m in sources and m not in done and r['exit_code']==0
   assert r['object_sha256']==sha(build/(m.replace('.','/')+'.olean'))==sources[m]['accepted_object_sha256'],m
   assert r['log_sha256']==sha(logs/(m+'.log')),m
   done.add(m); pending.remove(m)
  assert all(i in done for m in done for i in sources[m]['imports'] if i in sources),'Incomplete checkpoint dependency graph'
 else:
  write(out/'checkpoint.json',dict(project_manifest_sha256=sha(ROOT/'metadata/project.json'),compiler_sha256=sha(lean),prior_elapsed_seconds=0))
 def compile_one(m):
  r=sources[m]; src=ROOT/r['source']; obj=build/(m.replace('.','/')+'.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
  t=time.time(); proc=subprocess.run([str(lean),'-j','2','-o',str(obj),str(src.relative_to(ROOT/'src'))],cwd=ROOT/'src',env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
  log=logs/(m+'.log'); log.write_text(proc.stdout+proc.stderr,encoding='utf-8')
  return dict(module=m,exit_code=proc.returncode,seconds=round(time.time()-t,3),object_sha256=sha(obj) if obj.exists() else None,accepted_object_sha256=r['accepted_object_sha256'],log_sha256=sha(log))
 print('FRESH_BUILD',len(rows),'project modules;',args.jobs,'workers;',version,flush=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
  while pending or running:
   for m in sorted(pending):
    if len(running)>=args.jobs: break
    if all(i in done for i in sources[m]['imports'] if i in sources): pending.remove(m); running[pool.submit(compile_one,m)]=m
   assert running,('Unresolved import cycle',sorted(pending))
   finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in finished:
    m=running.pop(f); r=f.result(); receipts.append(r)
    with (out/'receipts.jsonl').open('a',encoding='utf-8') as journal: journal.write(json.dumps(r)+'\n')
    write(out/'progress.json',dict(done=len(receipts),total=len(rows),latest=r,elapsed_seconds=round(time.time()-start)))
    if r['exit_code']:
     write(out/'result.json',dict(status='failed',failed=r,receipts=receipts)); raise RuntimeError('Compile failed: '+m+'; see '+str(logs/(m+'.log')))
    done.add(m)
    if len(done)%25==0: print('COMPILED',len(done),'/',len(rows),'seconds',round(time.time()-start),flush=True)
 roots=[
  'AASCKleinGordon.CanonicalLicensing.kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger',
  'AASCKleinGordon.CanonicalLicensing.SRIntegration.kernel_faithful_native_sr_canonical_licensing_eh_scalar',
  'AASCKleinGordon.CurvedKG.kernel_faithful_same_eh_curved_kg_complete',
  'AASCKleinGordon.SameActionSource.kernel_faithful_same_action_kg_source',
  'AASCKleinGordon.RecoveryComparison.kernel_faithful_recovery_comparison',
  'AASCKleinGordon.OperationalSR.kernel_faithful_operational_sr']
 audit=out/'EndpointAudit.lean'; audit.write_text('import KernelFaithfulOperationalSR\n'+''.join('#check '+r+'\n#print axioms '+r+'\n' for r in roots),encoding='utf-8')
 p=subprocess.run([str(lean),str(audit)],env=env,cwd=out,capture_output=True,text=True,encoding='utf-8',errors='replace')
 (out/'endpoint-audit.log').write_text(p.stdout+p.stderr,encoding='utf-8'); assert p.returncode==0,p.stdout+p.stderr
 assert 'sorryAx' not in p.stdout and 'Lean.ofReduceBool' not in p.stdout,p.stdout
 axiom_reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',p.stdout,re.S)
 assert len(axiom_reports)==len(roots),p.stdout
 for report in axiom_reports: assert {x.strip() for x in report.split(',')}<={'propext','Quot.sound','Classical.choice'},report
 result=dict(status='passed',scope=mode,compiler_version=version,compiler_sha256=sha(lean),project_modules=len(rows),fresh_project_objects=len(receipts),byte_identical_objects=sum(r['object_sha256']==r['accepted_object_sha256'] for r in receipts),elapsed_seconds=round(time.time()-start)+prior_elapsed,resumed_verified_project_build=args.resume,endpoint_audit_exit_code=p.returncode,receipts=receipts,dependency_or_toolchain_bootstrap_tested=False)
 write(out/'result.json',result); print('PASSED',len(rows),'modules',result['byte_identical_objects'],'byte-identical',flush=True)
if __name__=='__main__': main()
