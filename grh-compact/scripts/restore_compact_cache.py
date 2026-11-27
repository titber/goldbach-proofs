"""Optional restore for the 72fead10 compact proof (Mathlib is restored separately).
Pass the grh-compact directory of a clean 5ba9208 cache reference checkout.
The cache receipt is not evidence of the application theorem: compile it locally.
"""
import subprocess as sp, json, hashlib, importlib.util, os, shutil, sys, tomllib
from pathlib import Path
REF='5ba920829cb7286b51f4d233b493f5b1287bf51b'
BASE='72fead102f663d5c7a407964a13dc0cf9d977207'
root=Path(__file__).resolve().parents[1]
ref=Path(sys.argv[1]).resolve()
def git(p,*a):return sp.check_output(['git','-C',str(p),*a]).decode().strip()
assert git(ref,'rev-parse','HEAD')==REF
assert 'version 4.35.0,' in sp.check_output(['lean','--version']).decode()
spec=importlib.util.spec_from_file_location('cache_tools',ref/'scripts/ci-cache-get.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
identity=cc.current_identity(ref)
assert identity['source_tree']==git(root,'rev-parse',BASE+':grh-compact/src')
sp.run(['git','diff','--quiet',BASE,'--','src/Lib','src/New','src/Main.lean','src/Statements.lean','lakefile.toml','lake-manifest.json','lean-toolchain'],cwd=root,check=True)
def blob(p):return p.read_bytes().replace(b'\r\n',b'\n')
for p in ('lean-toolchain','lake-manifest.json'):
    assert blob(root/p)==blob(ref/p)
for field in ('name','srcDir','moreLeanArgs','leanOptions','require','lean_lib'):
    l=lambda r:tomllib.loads((r/'lakefile.toml').read_text()).get(field)
    assert l(root)==l(ref),field
def fetch(k,maxsize):
    b=sp.check_output(['curl','-fsSL','--retry','3','--max-time','100','-A',cc.USER_AGENT,cc.PUBLIC_BASE+'/'+k])
    assert len(b)<=maxsize
    return b
rec=cc.find_record(identity,fetch)
assert rec
_,shas,mods=cc.validated_blobs(rec,identity,lambda k,n=cc.MAX_JSON:fetch(k,n))
for name,_,_ in mods:
    src=Path('src',*name.split('.')).with_suffix('.lean')
    assert blob(root/src)==blob(ref/src),name
print('Verified input fingerprint',cc.fingerprint(identity),'modules',len(mods),flush=True)
cache=root/'.lake/compact-artifacts'; out=cache/'artifacts'; out.mkdir(parents=True,exist_ok=True)
def good(p,h):return p.is_file() and hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==h
missing=[n for n,h in shas.items() if not good(out/n,h)]
for off in range(0,len(missing),100):
    batch=missing[off:off+100]; config=cache/'transfer.cfg'
    config.write_text(''.join('url = "'+cc.PUBLIC_BASE+'/artifacts/'+cc.SCOPE+'/'+n[:-5]+'.art"\noutput = "'+(out/(n+'.part')).as_posix()+'"\n' for n in batch))
    sp.run(['curl','-fsSL','--retry','3','--retry-all-errors','--connect-timeout','20','--max-time','120','--parallel','--parallel-max','24','-A',cc.USER_AGENT,'--config',str(config)],check=True)
    for n in batch:
        p=out/(n+'.part')
        if not good(p,shas[n]):raise ValueError('artifact digest: '+n)
        p.replace(out/n)
    print('verified archives',off+len(batch),'/',len(missing),flush=True)
jobs=cc.unpack_jobs(root,cache,mods)
for d in {d for j in jobs for d in j['base']}:Path(d).mkdir(parents=True,exist_ok=True)
cc.clear_output_hashes(root,mods)
sp.run(['leantar','--jobs','3','-f','-x','-j','-'],input=json.dumps(jobs),text=True,cwd=root,check=True)
print('Extracted',len(jobs),'modules; Lake must independently check its build inputs.',flush=True)
