from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
import first_release as fr
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
old=BASE/'environment-verification-source72d341e7';prior=json.loads((old/'result.json').read_bytes())
assert prior['inputs_unchanged'] and prior['steps'][0]['exit_code']==prior['steps'][1]['exit_code']==0
out=fr.new_output(ROOT,BASE/'independent-consumer-corrected-source72d341e7');src=out/'src';src.mkdir()
source=src/'IndependentCutoffTimeConsumer.lean'
text=(old/'src/IndependentCutoffTimeConsumer.lean').read_text().replace('namespace CutoffIndependentConsumer','namespace LowEnergy.CutoffIndependentConsumer').replace('end CutoffIndependentConsumer','end LowEnergy.CutoffIndependentConsumer')
source.write_text(text)
inputs=json.loads((old/'input-before.json').read_bytes())['files']
inputs={path:digest for path,digest in inputs.items() if not path.startswith(old.relative_to(ROOT).as_posix()+'/src/')}
inputs[source.relative_to(ROOT).as_posix()]=sha(source);inputs[Path(__file__).relative_to(ROOT).as_posix()]=sha(Path(__file__))
inputs[(old/'result.json').relative_to(ROOT).as_posix()]=sha(old/'result.json')
object_path=old/'lib'/Path(prior['public_path'].removeprefix('Lean/')).with_suffix('.olean')
inputs[object_path.relative_to(ROOT).as_posix()]=sha(object_path)
def capture():return {'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'files':{p:sha(ROOT/p) for p in inputs}}
before=capture();assert before['files']==inputs;write(out/'input-before.json',before);(out/'invocation-source.py').write_bytes(Path(__file__).read_bytes())
settings=fr.settings(ROOT);flags=list(dict.fromkeys(settings['package_moreLeanArgs']+settings['package_weakLeanArgs']+['--trust=0','-DwarningAsError=true']))
env=fr.build_environment();assert env['LEAN_NUM_THREADS']=='2';path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT/'Lean',text=True).strip();env['LEAN_PATH']=str(old/'lib')+':'+path
command=['lean','--root='+str(src),*flags,str(source),'-o',str(out/'consumer.olean')];write(out/'command.json',{'command':command,'cwd':'Lean','LEAN_NUM_THREADS':'2','LEAN_PATH':env['LEAN_PATH'],'settings':settings})
start=time.monotonic()
with (out/'consumer.log').open('x') as stream:
 p=subprocess.Popen(command,cwd=ROOT/'Lean',env=env,stdout=stream,stderr=subprocess.STDOUT);write(out/'handle.json',{'controller_pid':os.getpid(),'lean_pid':p.pid});status=p.wait()
after=capture();write(out/'input-after.json',after)
result={'schema':'h0mework/private-cutoff-time-independent-consumer@1','ok':status==0 and before['files']==after['files'],'exit_code':status,
        'inputs_unchanged':before['files']==after['files'],'head_before':before['head'],'head_after':after['head'],
        'elapsed_seconds':round(time.monotonic()-start,3),'formal_acceptance':False,'candidate_result':(old/'result.json').relative_to(ROOT).as_posix(),
        'candidate_result_sha256':sha(old/'result.json'),'original_fixture_failure_preserved':True,'fixture_correction':'Place the independent fixture under LowEnergy, preserving the original namespace resolution; no producer change.',
        'source_sha256':sha(source),'candidate_object_sha256':sha(object_path),'log_sha256':sha(out/'consumer.log')}
write(out/'result.json',result);print(json.dumps(result),flush=True);raise SystemExit(0 if result['ok'] else 1)
