"""Native, serial replay of the upstream compact GRH proof and this application.
Run: lake exe cache get; lake env python scripts/verify_binary_shift.py
No foreign olean search path is added. Each compiler invocation uses src as its
module root. The two applications are compiled only after their prerequisite.
"""
import os, sys, subprocess, re, hashlib, json, shutil
from pathlib import Path
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1]; os.chdir(ROOT)
SRC=ROOT/'src'
ART=ROOT/'.lake/build/lib/lean'
LOG=ROOT/'.lake/binary-shift-replay'
LOG.mkdir(parents=True,exist_ok=True)
LEAN=shutil.which('lean')
def check(*a):
    return subprocess.check_output(a,text=True,encoding='utf-8').strip()
version=check(LEAN,'--version')
print(version,flush=True)
assert 'version 4.35.0,' in version, version
assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
base='72fead102f663d5c7a407964a13dc0cf9d977207'
pristine=['src/Lib','src/New','src/Statements.lean','src/Main.lean','Challenge.lean','lake-manifest.json','lakefile.toml','lean-toolchain']
subprocess.run(['git','diff','--exit-code',base,'--',*pristine],check=True)
lock=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
pins={i['name']:i['rev'] for i in lock}
assert pins['mathlib']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
for n,rev in pins.items():
    assert check('git','-C',str(ROOT/'.lake/packages'/n),'rev-parse','HEAD')==rev,n
prefix=Path(check(LEAN,'--print-prefix')).resolve()
for p in os.environ.get('LEAN_PATH','').split(os.pathsep):
    if p:
        path=Path(p).resolve()
        assert path.is_relative_to(ROOT) or path.is_relative_to(prefix), 'Unexpected LEAN_PATH: '+p
artrel=lambda m:Path(*m.split('.'))
def source(m):return SRC/artrel(m).with_suffix('.lean')
names=['PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density','CheckerSuite.GRHConsumer','Conjectures.Goldbach.BinaryShiftExceptionUnion']
order=[]; deps={}
def visit(m):
    if m in deps:return
    p=source(m)
    imports=re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)',p.read_text(encoding='utf-8-sig'),re.M)
    deps[m]=list(dict.fromkeys(x for x in imports if source(x).is_file()))
    for x in deps[m]:visit(x)
    order.append(m)
density_only='--density-only' in sys.argv
for m in ([names[0]] if density_only else [names[1], names[0], names[2]]): visit(m)
flags=['--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-DmaxHeartbeats=4000000']
@lru_cache(None)
def key(m):
    return hashlib.sha256((version+repr(pins)+repr(flags)+''.join(key(x) for x in deps[m])).encode()+source(m).read_bytes()).hexdigest()
def runlean(m,p,args,upstream):
    out=LOG/(m+'.log')
    cmd=[LEAN,'-j'+os.environ.get('GRH_LEAN_THREADS','3'),('--root=src' if p.is_relative_to(SRC) else '--root=.'),*(flags if upstream else []),*args,str(p)]
    with out.open('wb') as f:
        r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    print(f'exit={r.returncode} {m} log={out}',flush=True)
    if r.returncode:
        print(out.read_text(encoding='utf-8',errors='replace')[-2600:],flush=True)
        sys.exit(r.returncode)
    return out
cached='--validated-cache' in sys.argv
if cached:
    r=subprocess.run(['lake','build','--no-build','+Main:olean'])
    print(f'exit={r.returncode} lake build --no-build +Main:olean',flush=True)
    if r.returncode:sys.exit(r.returncode)
print('Density-only build.' if density_only else f'Native source closure: {len(order)} modules. GRH consumer, density, frozen application, audit.',flush=True)
for i,m in enumerate(order,1):
    o=ART/artrel(m).with_suffix('.olean')
    if cached and m not in names:
        assert o.is_file(),m
        continue
    mark=LOG/(m+'.ok')
    if o.is_file() and mark.is_file() and mark.read_text()==key(m):
        continue
    print(f'BEGIN {i}/{len(order)} {m}',flush=True)
    o.parent.mkdir(parents=True,exist_ok=True)
    runlean(m,source(m),['-o',str(o)],not (m.startswith('PEqualNP.') or m.startswith('Conjectures.')))
    tmp=mark.with_suffix('.part');tmp.write_text(key(m));tmp.replace(mark)
if density_only: sys.exit(0)
# The audit has an independent copy of the frozen type and uses no GRH binder.
au=ROOT/'scripts/AuditBinaryShift.lean'
out=runlean('audit',au,[],False)
report=out.read_text(encoding='utf-8')
for n in ('LFunction_eq_zero_re','Conjectures.Goldbach.BinaryShiftExceptionUnion'):
    hit=re.search(re.escape("'"+n+"'")+r' depends on axioms:\s*\[([^\]]+)\]',report)
    assert hit and {a.strip() for a in hit[1].split(',')}=={'propext','Classical.choice','Quot.sound'},n
print(report,flush=True)
