"""Stage and roll the material successor without changing any historical source."""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
import copy
import fcntl
import importlib.util
import json
from pathlib import Path
import shlex
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from crypto import digest
from recovery_loop import save
import material_extension


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


prior = module('material_prior_deploy', 'public-supply-deploy.py')
roll, execute, load, sha = prior.roll, prior.execute, prior.load, prior.sha


def location(box): return box/'ha/regeneration/refeed'


def context(config, source):
    value = prior.context(config, source)
    for name in ('refeed', 'material_extension'):
        if name in config: value[name] = copy.deepcopy(config[name])
    return value


def prepare(box):
    home = location(box); manifest = load(box/'ha/deployment.json')
    if not (home/'online-before.json').exists(): save(home/'online-before.json', manifest)
    source = load(home/'bundle/candidate.json')['refeed']; inventory = load(source['closure'])
    protocol = {name:sha(NETWORK/name) for name in sorted(set(manifest['protocol']) |
        set(manifest.get('application_receipts', {}).get('protocol', {})) |
        {'material_extension.py', 'material_regeneration.py', 'material_readiness.py'})}
    revision = digest(protocol)
    logical = sum((Path(source['lean_path'])/n).stat().st_size for n in inventory)
    plan = load(home/'resource-plan.json'); plan.update(source_view_logical_bytes=logical,
        allocation='existing immutable dependency hardlinks; transfer changed artifacts only')
    save(home/'resource-plan.json', plan)

    def stage(member):
        receipt = home/('staged-'+member+'.json')
        if receipt.exists():
            value = load(receipt)
            if value['entry']['config']['refeed']['descriptor'] != source['descriptor']:
                raise ValueError('MATERIAL_STAGED_SOURCE_CHANGED')
            if value['revision'] == revision: return member, value['entry']
            # A later protocol-only fix keeps the already paid source view and votes.
        if member == 'a':
            cfg = load(box/'local-anchor/config.json'); root = str(home/'bundle'); code = str(NETWORK)
            settings = copy.deepcopy(source); tool = cfg['semantic']['backend'][0]
            exporter = Path(root)/'scripts/verification/public-material-network-source.lean'
            prior.same_file(exporter, Path(source['exporter']).read_bytes())
            settings['exporter']=str(exporter);settings['backend'][4]=str(exporter);settings['cwd']=root
        else:
            item = manifest['nodes'][member]
            cfg = json.loads(execute(member, 'from pathlib import Path\nprint(Path('+repr(item['home']+'/config.json')+').read_text())', manifest, 60))
            root = item['home']+'/material/source-'+digest(source['descriptor'])
            code = item['home']+'/code/'+revision+'/Verification/public-audit/network'
            roots = [cfg[name]['lean_path'] for name in ('regeneration','semantic','governance','energy','continuation','handoff')]
            payload = {name:base64.b64encode((NETWORK/name).read_bytes()).decode() for name in protocol}
            script = f'''import base64,hashlib,json,os,shutil
from pathlib import Path
lib=Path({root!r})/'lib';lib.mkdir(parents=True,exist_ok=True)
inventory={inventory!r};roots={roots!r};missing=[]
for n,w in inventory.items():
 p=lib/n
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==w:continue
 candidates=[Path(r)/n for r in roots if (Path(r)/n).is_file() and hashlib.sha256((Path(r)/n).read_bytes()).hexdigest()==w]
 original=next((p for p in candidates if p.stat().st_dev==lib.stat().st_dev),next(iter(candidates),None))
 if original is None:missing.append(n);continue
 p.parent.mkdir(parents=True,exist_ok=True)
 if original.stat().st_dev==lib.stat().st_dev:os.link(original,p)
 else:shutil.copyfile(original,p)
for n,v in {payload!r}.items():
 p=Path({code!r})/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v)
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
print(json.dumps(dict(missing=missing)))
'''
            missing = json.loads(execute(member, script, manifest, 600))['missing']
            save(home/('transfer-'+member+'.json'), dict(files=len(missing), bytes=sum((Path(source['lean_path'])/n).stat().st_size for n in missing)))
            if missing:
                archive = home/('transfer-'+member+'.tar')
                with tarfile.open(archive, 'w') as tar:
                    for name in missing: tar.add((Path(source['lean_path'])/name).resolve(), arcname=name, recursive=False)
                receiver = f'''import hashlib,sys,tarfile
from pathlib import Path
lib=Path({root!r})/'lib';inventory={inventory!r};tar=tarfile.open(fileobj=sys.stdin.buffer,mode='r|');count=0
for item in tar:
 if not item.isfile() or item.name not in inventory:raise ValueError('MATERIAL_ARCHIVE_SCOPE')
 p=lib/item.name;p.parent.mkdir(parents=True,exist_ok=True);temporary=p.with_name(p.name+'.incoming')
 with temporary.open('wb') as out:
  stream=tar.extractfile(item)
  while True:
   data=stream.read(1048576)
   if not data:break
   out.write(data)
 if hashlib.sha256(temporary.read_bytes()).hexdigest()!=inventory[item.name]:raise ValueError('MATERIAL_ARTIFACT_HASH')
 temporary.replace(p);count+=1
print(count)
'''
                receiver_path = root+'/receive.py'
                execute(member, 'from pathlib import Path\nPath('+repr(receiver_path)+').write_text('+repr(receiver)+')', manifest, 60)
                node = roll.spare.transport.node(member)
                with archive.open('rb') as stream:
                    result = node._run_remote(node.remote_argv(item['python'], receiver_path), allow_probe=False,
                        stdin=stream, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900)
                if result.returncode or int(result.stdout) != len(missing): raise RuntimeError('MATERIAL_TRANSFER:'+result.stderr.decode()[-1000:])
                archive.unlink()
                execute(member, 'from pathlib import Path\nPath('+repr(receiver_path)+').unlink()', manifest, 60)
            exporter = ROOT/'Lean/scripts/verification/public-material-network-source.lean'
            files = {'closure.json':Path(source['closure']).read_bytes(), 'scripts/verification/'+exporter.name:exporter.read_bytes()}
            execute(member, 'import base64\nfrom pathlib import Path\n'+
                '\n'.join('p=Path('+repr(root+'/'+name)+');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode('+repr(base64.b64encode(raw).decode())+'))' for name,raw in files.items()), manifest, 120)
            tool = cfg['semantic']['backend'][0]
            settings = dict(descriptor=source['descriptor'], exporter=root+'/scripts/verification/'+exporter.name,
                closure=root+'/closure.json', lean_path=root+'/lib', cwd=root, error_log=root+'/source.log',
                backend=[tool,'--trust=0','-j1','--run',root+'/scripts/verification/'+exporter.name,'private-one'], native_call_seconds=300)
        cfg['refeed'] = settings; cfg['semantic']['governance_context'] = context(cfg, manifest['source'])
        cfg['semantic']['replay_seconds'] = 300
        candidate = root+'/material-candidate.json'
        script = 'import json,sys,hashlib\nfrom pathlib import Path\nsys.path.insert(0,'+repr(code)+')\nfrom source_semantics import Engine\nc='+repr(cfg)+'\nEngine(c["refeed"])\nPath('+repr(candidate)+').write_text(json.dumps(c,sort_keys=True)+"\\n")\nprint(hashlib.sha256(Path('+repr(tool)+').read_bytes()).hexdigest())'
        compiler_hash = execute(member, script, manifest, 300).strip()
        entry = dict(config=cfg, candidate=candidate, root=root, code=code, compiler_sha256=compiler_hash)
        save(receipt, dict(revision=revision, entry=entry)); print('MATERIAL SOURCE STAGED',member,flush=True)
        return member,entry

    with ThreadPoolExecutor(max_workers=4) as pool: nodes = dict(pool.map(stage, 'abcd'))
    save(home/'prepared.json', dict(revision=revision, protocol=protocol, nodes=nodes, descriptor=source['descriptor']))


def readiness(box):
    home = location(box); prepared = load(home/'prepared.json'); manifest = load(home/'online-before.json')
    def attest(member):
        path=home/('ready-'+member+'.json')
        if path.exists(): return load(path)['vote']
        entry=prepared['nodes'][member]; evidence=entry['root']+'/material-readiness'; check=entry['root']+'/material-independent'
        script=f'''import json,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
import material_readiness as p
c=json.loads(Path({entry['candidate']!r}).read_text());e=Path({evidence!r});q=Path({check!r})
if not (e/'vote.json').exists():p.issue(c,e)
if not (q/'acceptance.json').exists():p.check(c,e,q)
print(json.dumps(dict(vote=json.loads((e/'vote.json').read_text()),acceptance=json.loads((q/'acceptance.json').read_text()),evidence=str(e),independent=str(q))))
'''
        value=json.loads(execute(member,script,manifest,1600));save(path,value)
        print('INDEPENDENT MATERIAL READINESS PASS',member,value['acceptance']['prefix']['seq'],flush=True)
        return value['vote']
    with ThreadPoolExecutor(max_workers=4) as pool: votes=list(pool.map(attest,'abcd'))
    certificate=dict(point=votes[0]['receipt']['body']['point'],votes=votes)
    material_extension.admission(prepared['nodes']['a']['config'],certificate)
    save(home/'admission.json',certificate)


def install(box):
    home=location(box);lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    prepared=load(home/'prepared.json');before=load(home/'online-before.json');certificate=load(home/'admission.json')
    if prepared['protocol']!={n:sha(NETWORK/n) for n in prepared['protocol']}:raise ValueError('MATERIAL_CODE_CHANGED')
    if (home/'installed.json').exists():
        current=load(box/'ha/deployment.json')
        if current['material']['admission']!=digest(certificate):raise ValueError('MATERIAL_INSTALL_CHANGED')
        print('PAID MATERIAL INSTALL RETAINED',flush=True);return
    manifest=copy.deepcopy(before);prefix=certificate['point']['prefix']
    literal=roll.spare.rows(before['mac']['service']['database'])
    if dict(seq=len(literal),head=literal[-1][2])!=prefix:raise ValueError('MATERIAL_PARENT_MOVED')
    progress=load(home/'install-progress.json') if (home/'install-progress.json').exists() else {'stages':[]}
    def paid(stage):
        if stage not in progress['stages']:progress['stages'].append(stage)
        save(home/'install-progress.json',progress);print('MATERIAL ROLL',stage,flush=True)
    configs={};services={}
    for member,entry in prepared['nodes'].items():
        cfg=copy.deepcopy(entry['config']);cfg['material_extension']=certificate
        cfg['semantic']['governance_context']=context(cfg,manifest['source']);material_extension.admission(cfg);configs[member]=cfg
        if member!='a':manifest['nodes'][member].update(code=entry['code'],protocol=prepared['protocol'])
    inventory=load(prepared['nodes']['a']['config']['refeed']['closure'])
    for owner,member in [('mac','a'),('spark','c')]:
        cfg=copy.deepcopy(before[owner]['service']);entry=prepared['nodes'][member]
        cfg.update(refeed=configs[member]['refeed'],material_extension=certificate)
        settings=cfg['refeed'];worker=dict(command=[settings['backend'][0],'--trust=0','-j1','-DElab.async=false',
            '-DwarningAsError=true','--run','scripts/verification/public-material-network-source.lean','public'],
            cwd=settings['cwd'],lean_path=settings['lean_path'],stderr=entry['root']+'/public-worker.stderr',
            compiler_sha256=entry['compiler_sha256'],contract='complete-default-material-privacy/v1',timeout=300)
        inputs={settings['exporter']:settings['descriptor']['exporter_sha256'],settings['closure']:settings['descriptor']['closure_sha256']}
        inputs.update({settings['lean_path']+'/'+n:w for n,w in inventory.items()})
        cfg['online_privacy']={**cfg['online_privacy'],'worker':worker,'source_inputs':inputs};services[owner]=cfg
    if 'writer-barrier' not in progress['stages']:
        frozen={}
        try:
            for owner in ('spark','mac'):
                frozen[owner]=roll.freeze_writer(box,before,owner);save(home/'writer-barrier.json',frozen)
            from ha_quorum import Quorum
            end=time.monotonic()+30
            while True:
                states=Quorum(before['mac']['service']).collect('status')
                if set(states)==set('abcd') and all(not v['intents'] and {k:v['head'][k] for k in ('seq','head')}==prefix for v in states.values()):break
                if time.monotonic()>=end:raise ValueError('MATERIAL_ROLL_BARRIER')
                time.sleep(.5)
            save(home/'barrier-status.json',states);paid('writer-barrier')
        except BaseException:
            for owner,record in frozen.items():roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            raise
    frozen=load(home/'writer-barrier.json')
    try:
        from ha_quorum import Quorum
        for member in 'bcd':
            if 'anchor-'+member in progress['stages']:continue
            item=manifest['nodes'][member]
            execute(member,'from pathlib import Path\nPath('+repr(item['home']+'/config.json')+').write_text('+repr(json.dumps(configs[member])+'\n')+')',manifest,90)
            roll.restart_anchor(member,manifest);end=time.monotonic()+360;client=Quorum(before['mac']['service']).nodes[member]
            while time.monotonic()<end:
                try:
                    state=client.call('semantic-status')
                    if state['prefix']==prefix and state['backend'] and not state['warm_error']:break
                except (ValueError,OSError,EOFError):pass
                time.sleep(2)
            else:raise TimeoutError('MATERIAL_VOTER_NOT_READY:'+member)
            paid('anchor-'+member)
        save(box/'local-anchor/config.json',configs['a'])
        for owner in ('mac','spark'):
            manifest[owner]['service']=services[owner];manifest[owner]['controller']['release']=prepared['revision']
        for owner in ('spark','mac'):
            if 'candidate-'+owner in progress['stages']:continue
            prior.retire_writer(box,before,owner,frozen[owner])
            if owner=='spark':
                item=manifest['nodes']['c'];command=[item['python'],item['code']+'/live_timing.py','coordinator',item['home']+'/ha/controller.json']
                script=f'''from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'runtime/STOP').unlink(missing_ok=True)
(p/'service.json').write_text({json.dumps(services[owner])!r}+'\\n')
(p/'controller.json').write_text({json.dumps(manifest[owner]['controller'])!r}+'\\n')
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
'''
                execute('c',script,manifest,60)
                roll.spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
            else:
                roll.module('material_stop','public-recovery-isolation.py').stop(box)
                save(box/'ha/mac/service.json',services[owner]);save(box/'ha/mac/controller.json',manifest[owner]['controller'])
                (box/'runtime/STOP').unlink(missing_ok=True)
                subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            paid('candidate-'+owner)
        manifest.update(protocol=prepared['protocol'],release=prepared['revision'],material=dict(descriptor=prepared['descriptor'],evidence=str(home),admission=digest(certificate)))
        manifest['public_timing']['release']=prepared['revision']
        manifest['application_receipts']['protocol']=prepared['protocol']
        for owner,member in [('mac','a'),('spark','c')]:manifest['application_receipts']['candidates'][owner]['code']=prepared['nodes'][member]['code']
        for member in 'abcd':manifest['semantic']['configurations'][member]=configs[member]['semantic']
        save(box/'ha/deployment.json',manifest)
        if roll.spare.rows(manifest['mac']['service']['database'])!=literal:raise ValueError('MATERIAL_ROLL_CHANGED_JOURNAL')
        save(home/'installed.json',dict(prefix=prefix,release=prepared['revision'],admission=digest(certificate),original_admission=digest(before['native_admission']),stages=progress['stages'],activated=False))
        print('MATERIAL SOURCE INSTALLED: original45 unchanged; control event required',flush=True)
    except BaseException:
        save(home/'install-failed.json',dict(at=time.time(),stages=progress['stages']))
        for owner,record in frozen.items():
            try:roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            except (OSError,ValueError,RuntimeError,subprocess.SubprocessError):pass
        raise


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('operation',choices=['prepare','readiness','install']);p.add_argument('box',type=Path);a=p.parse_args()
    globals()[a.operation](a.box.resolve())
