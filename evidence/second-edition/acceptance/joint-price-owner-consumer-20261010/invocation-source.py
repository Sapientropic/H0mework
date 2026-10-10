from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,subprocess,sys,time

ROOT=Path(__file__).resolve().parents[3]
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
import first_release as fr
import source_view as sv


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path,data):path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')


def main():
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    assert head=='72d341e7964e6ba09755edf9601805e75b38ff56'
    plan_path=BASE.parent/'physics-runtime-overlap-plan-72d341e7.json'
    plan=json.loads(plan_path.read_bytes())
    selected=next(p for p in plan['packages'] if p['id']=='v2-9c73-prepared-actual')
    ex=json.loads((ROOT/'tools/export-map.json').read_bytes())
    inverse={r['target']:r for r in ex['modules']}
    suffix='/SourceMasterCorrectionJointPrice.lean'
    rows=[r for r in ex['modules'] if r['path'].endswith(suffix)]
    assert len(rows)==6
    current=next(r for r in rows if '/R9c73a630/' in r['path'])
    prefix=current['target'].rsplit('.',1)[0]+'.'
    raw=(ROOT/current['path']).read_text()
    rules=[{'source_owner':'_private.'+stem,'target_owner':'_private.'+prefix+stem}
           for stem in ('SourceJointRadialSpatialReturn','SourceJointRadialPrice')]
    candidate=raw
    for rule in rules:
        before='"'+rule['source_owner']+'."';after='"'+rule['target_owner']+'."'
        assert candidate.count(before)==1
        candidate=candidate.replace(before,after)
    recovered=candidate
    for rule in reversed(rules):recovered=recovered.replace('"'+rule['target_owner']+'."','"'+rule['source_owner']+'."')
    assert recovered==raw
    view,original=sv.module_views(current,inverse)
    assert hashlib.sha256(original).hexdigest()==current['source_sha256']
    out=fr.new_output(ROOT,BASE/'environment-verification-72d341e7')
    src=out/'src';lib=out/'lib';src.mkdir();lib.mkdir()
    source_path=src/Path(current['target'].replace('.','/')).with_suffix('.lean')
    source_path.parent.mkdir(parents=True);source_path.write_text(candidate)
    reserved=Path(current['target'].replace('.','/')).with_suffix('.olean')
    ancestors=set(reserved.parents)
    def link_cache(public,private,relative=Path('.')):
        private.mkdir(exist_ok=True)
        for child in public.iterdir():
            rel=relative/child.name
            if rel.parent==reserved.parent and child.name.startswith(reserved.stem+'.'):continue
            dest=private/child.name
            if rel in ancestors:link_cache(child,dest,rel)
            else:dest.symlink_to(child,target_is_directory=child.is_dir())
    link_cache(ROOT/'Lean/.lake/build/lib/lean',lib)
    probe=src/'OriginalGeometryOwners.lean'
    wanted=['LowEnergy.PreparationPhysicalJointRadialForcing.spatial_positive',
            'LowEnergy.PreparationPhysicalJointRadialForcing.physical_price_shape']
    expected=[prefix+'SourceJointRadialSpatialReturn',prefix+'SourceJointRadialPrice']
    probe.write_text('import '+prefix+'SourceMasterSimpleNumerator\nimport Lean\nset_option autoImplicit false\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  for (text, owner) in '+json.dumps(list(zip(wanted,expected))).replace('["','("').replace('"]','")')+' do\n    let wanted := text.toName\n    let candidates := env.constants.toList.filter fun (name, _) => privateToUserName name == wanted\n    logInfo m!"ALL {wanted}: {candidates.map Prod.fst}"\n    let exact := candidates.filter fun (name, _) => name.toString.startsWith ("_private." ++ owner ++ ".")\n    unless exact.length == 1 do throwError "Expected one actual producer {owner}: {exact.map Prod.fst}"\n    let (name, info) := exact[0]!\n    let some index := env.getModuleIdxFor? name | throwError "No module for {name}"\n    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong module {name}"\n    unless (info.value? true).isSome do throwError "No checked value {name}"\n    logInfo m!"OWNER {wanted} = {name} MODULE {env.header.moduleNames[index]!}"\n    logInfo m!"TYPE {name} = {info.type}"\n')
    opening=raw[:raw.index('open Lean Elab Term in')]
    opening=opening.replace('local instance CorrectionPriceIndex','local instance IndependentCorrectionPriceIndex')
    consumer=src/'IndependentJointPriceConsumer.lean'
    text='import '+current['target']+'\n'+opening[opening.index('set_option autoImplicit'):]
    for name,args in (
        ('sourceCorrectionInverse_return','n nonzero zeta i'),
        ('sourceDenominatorCorrection_fourier_bound','q c eta frequency causal d radial l r i test x n nonzero'),
        ('sourceDenominatorCorrection_spatial_zero','q c eta frequency causal l r i test x'),
    ):
        assert raw.count('theorem '+name+' ')==1
        statement=raw.split('theorem '+name,1)[1].split(' := by',1)[0]
        text+='example'+statement+' := '+name+' '+args+'\n\n'
    text+='end LowEnergy.PreparationPhysicalMasterCorrectionReturn\n'
    for name in ('sourceCorrectionInverse_return','sourceDenominatorCorrection_fourier_bound','sourceDenominatorCorrection_spatial_zero'):
        text+='#print axioms LowEnergy.PreparationPhysicalMasterCorrectionReturn.'+name+'\n'
    consumer.write_text(text)
    settings=fr.settings(ROOT)
    flags=list(dict.fromkeys(settings['package_moreLeanArgs']+settings['package_weakLeanArgs']+['--trust=0','-DwarningAsError=true']))
    freeze_path=ROOT/'.local/acceptance-execution-20261010/cohort-freeze.json'
    freeze=json.loads(freeze_path.read_bytes());assert freeze['head']==head and not freeze.get('official_dispatch_hold')
    inputs=set(freeze['files'])|set(selected['source_files'])|{plan_path.relative_to(ROOT).as_posix(),Path(__file__).relative_to(ROOT).as_posix()}
    inputs.update(path.relative_to(ROOT).as_posix() for path in (source_path,probe,consumer))
    def capture():return {'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                          'files':{p:sha(ROOT/p) for p in sorted(inputs)},'cohort_freeze_sha256':sha(freeze_path)}
    before=capture();assert before['head']==head
    assert all(before['files'][p]==v for p,v in freeze['files'].items())
    assert all(before['files'][p]==v for p,v in selected['source_files'].items())
    write(out/'input-before.json',before);(out/'invocation-source.py').write_bytes(Path(__file__).read_bytes())
    original_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT/'Lean',text=True).strip()
    env=fr.build_environment();assert env['LEAN_NUM_THREADS']=='2';env['LEAN_PATH']=str(lib)+':'+original_path
    steps=[]
    def execute(label,path,object):
        command=['lean','--root='+str(src),*flags,str(path),'-o',str(object)]
        write(out/(label+'-command.json'),{'command':command,'cwd':'Lean','LEAN_NUM_THREADS':'2','LEAN_PATH':env['LEAN_PATH'],'settings':settings})
        begin=time.monotonic();log=out/(label+'.log');object.parent.mkdir(parents=True,exist_ok=True)
        with log.open('x') as stream:
            process=subprocess.Popen(command,cwd=ROOT/'Lean',env=env,stdout=stream,stderr=subprocess.STDOUT)
            write(out/'handle.json',{'controller_pid':os.getpid(),'lean_pid':process.pid,'step':label})
            code=process.wait()
        step={'name':label,'exit_code':code,'elapsed_seconds':round(time.monotonic()-begin,3),'command':command,'source_sha256':sha(path),'log_sha256':sha(log),'object_sha256':sha(object) if object.exists() else None}
        steps.append(step);write(out/'steps.json',steps);print(json.dumps(step),flush=True);return code==0
    ok=execute('actual-original-geometry-owners',probe,out/'owner-probe.olean')
    if ok:ok=execute('canonical-joint-price-candidate',source_path,lib/reserved)
    if ok:ok=execute('independent-joint-price-consumer',consumer,out/'consumer.olean')
    after=capture();write(out/'input-after.json',after)
    result={'schema':'h0mework/private-joint-price-owner-verification@1','ok':ok and before==after,'inputs_unchanged':before==after,
            'formal_acceptance':False,'head':head,'original_source_sha256':current['source_sha256'],'candidate_public_sha256':sha(source_path),
            'candidate_inverse_public_bytes_exact':True,'source_options':[line for line in raw.splitlines() if line.startswith('set_option ')],
            'candidate_rules':rules,'original_checked_owner_expectations':dict(zip(wanted,expected)),'steps':steps,'source_scope_sha256':selected['source_scope_sha256']}
    write(out/'result.json',result);print(json.dumps({'ok':result['ok'],'inputs_unchanged':result['inputs_unchanged'],'steps':len(steps)}),flush=True)
    return 0 if result['ok'] else 1

if __name__=='__main__':raise SystemExit(main())
