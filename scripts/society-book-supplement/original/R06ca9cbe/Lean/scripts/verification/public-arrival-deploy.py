"""Stage and roll the source-arrival successor without changing historical events."""
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
import productive_extension
import arrival_extension


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value


prior = module('productive_prior_deploy', 'public-supply-deploy.py')
roll, execute, load, sha = prior.roll, prior.execute, prior.load, prior.sha


def location(box): return box/'ha/regeneration/productive/external-arrival/online'


def context(config, source):
    value = prior.context(config, source)
    for name in ('refeed','material_extension','productive','productive_extension',
                 'arrival','arrival_extension'):
        if name in config: value[name] = copy.deepcopy(config[name])
    return value


def prepare(box):
    home = location(box); manifest = load(box/'ha/deployment.json')
    home.mkdir(parents=True, exist_ok=True)
    literal = [list(row) for row in roll.spare.rows(manifest['mac']['service']['database'])]
    if len(literal) != 68: raise ValueError('ARRIVAL_ORIGINAL_PREFIX_NOT_68')
    original = dict(rows=literal, prefix=dict(seq=len(literal), head=literal[-1][2]))
    original['digest'] = digest(original)
    productive_extension.require(manifest['mac']['service'], literal)
    before_path = home/'original-before.json'
    if before_path.exists():
        if load(before_path) != original: raise ValueError('ARRIVAL_ORIGINAL_PREFIX_CHANGED')
    else: save(before_path, original)
    manifest_path = home/'online-before.json'
    if manifest_path.exists():
        prior_manifest = load(manifest_path)
        if prior_manifest != manifest: raise ValueError('ARRIVAL_MANIFEST_CHANGED')
    else: save(manifest_path, manifest)
    before = load(manifest_path)
    if [list(row) for row in roll.spare.rows(before['mac']['service']['database'])] != literal:
        raise ValueError('ARRIVAL_ORIGINAL_PREFIX_NOT_CURRENT')
    source = load(home/load(home/'active-bundle.json')['directory']/'candidate.json')['arrival']; inventory = load(source['closure'])
    if len(source.get('backend', [])) != 6 or source['backend'][-1] != 'private-one':
        raise ValueError('ARRIVAL_BACKEND_SHAPE')
    protocol = {name:sha(NETWORK/name) for name in sorted(set(manifest['protocol']) |
        set(manifest.get('application_receipts', {}).get('protocol', {})) |
        {'source_extension.py', 'arrival_extension.py', 'arrival_regeneration.py',
         'arrival_readiness.py', 'source_semantics.py'})}
    revision = digest(protocol)
    logical = sum((Path(source['lean_path'])/n).stat().st_size for n in inventory)
    plan_path=home/'resource-plan.json'
    plan=load(plan_path) if plan_path.exists() else load(home.parents[1]/'resource-plan.json')
    plan.update(source_view_logical_bytes=logical,
        allocation='existing immutable dependency hardlinks; transfer changed artifacts only')
    save(plan_path, plan)

    def stage(member):
        receipt = home/('staged-'+member+'.json')
        if receipt.exists():
            value = load(receipt)
            if (value.get('descriptor') != source['descriptor']
                    or value.get('original_prefix') != original['prefix']
                    or value.get('original_digest') != original['digest']
                    or value['entry']['config'].get('arrival', {}).get('descriptor') != source['descriptor']
                    or len(value['entry']['config'].get('arrival', {}).get('backend', [])) != 6
                    or value['entry']['config']['arrival']['backend'][-1] != 'private-one'):
                raise ValueError('ARRIVAL_STAGED_SOURCE_CHANGED')
            if value['revision'] == revision: return member, value['entry']
            # The immutable source view was paid already; update protocol bytes only.
            entry=copy.deepcopy(value['entry'])
            if member!='a':
                entry['code']=manifest['nodes'][member]['home']+'/code/'+revision+'/Verification/public-audit/network'
                payload={name:base64.b64encode((NETWORK/name).read_bytes()).decode() for name in protocol}
                execute(member,'import base64\nfrom pathlib import Path\n'+
                    '\n'.join('p=Path('+repr(entry['code']+'/'+name)+');p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode('+repr(raw)+');assert not p.exists() or p.read_bytes()==raw;p.write_bytes(raw)' for name,raw in payload.items()),manifest,120)
            save(receipt,dict(revision=revision,entry=entry,reused_source_revision=value['revision'],
                              descriptor=source['descriptor'],original_prefix=original['prefix'],
                              original_digest=original['digest']))
            print('PAID ARRIVAL SOURCE RETAINED; PROTOCOL STAGED',member,flush=True)
            return member,entry
        if member == 'a':
            cfg = load(box/'local-anchor/config.json'); root = source['cwd']; code = str(NETWORK)
            settings = copy.deepcopy(source); tool = cfg['semantic']['backend'][0]
            exporter = Path(root)/'scripts/verification/public-arrival-network-source.lean'
            prior.same_file(exporter, Path(source['exporter']).read_bytes())
            if len(settings['backend']) != 6 or settings['backend'][-1] != 'private-one':
                raise ValueError('ARRIVAL_LOCAL_BACKEND_SHAPE')
            settings['exporter']=str(exporter);settings['backend'][4]=str(exporter);settings['cwd']=root
        else:
            item = manifest['nodes'][member]
            cfg = json.loads(execute(member, 'from pathlib import Path\nprint(Path('+repr(item['home']+'/config.json')+').read_text())', manifest, 60))
            root = item['home']+'/arrival/source-'+digest(source['descriptor'])
            code = item['home']+'/code/'+revision+'/Verification/public-audit/network'
            roots = [cfg[name]['lean_path'] for name in ('productive','refeed','regeneration','semantic','governance','energy','continuation','handoff')]
            if (home/'source-reuse.json').exists(): roots.append(load(home/'source-reuse.json')[member])
            payload = {name:base64.b64encode((NETWORK/name).read_bytes()).decode() for name in protocol}
            script = f'''import base64,hashlib,json,os,shutil
from pathlib import Path
lib=Path({root!r})/'lib';lib.mkdir(parents=True,exist_ok=True)
inventory={inventory!r};roots={roots!r};missing=[];copied_bytes=0;linked=0
free_before=shutil.disk_usage(lib).free
for n,w in inventory.items():
 p=lib/n
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==w:continue
 candidates=[Path(r)/n for r in roots if (Path(r)/n).is_file() and hashlib.sha256((Path(r)/n).read_bytes()).hexdigest()==w]
 original=next((p for p in candidates if p.stat().st_dev==lib.stat().st_dev),next(iter(candidates),None))
 if original is None:missing.append(n);continue
 p.parent.mkdir(parents=True,exist_ok=True)
 if original.stat().st_dev==lib.stat().st_dev:os.link(original,p);linked+=1
 else:
  if original.stat().st_size+512*1024**2>shutil.disk_usage(lib).free:raise ValueError('ARRIVAL_SOURCE_DISK_RESERVE')
  shutil.copyfile(original,p);copied_bytes+=original.stat().st_size
for n,v in {payload!r}.items():
 p=Path({code!r})/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v)
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
print(json.dumps(dict(missing=missing,free=shutil.disk_usage(lib).free,copied_bytes=copied_bytes,linked=linked)))
'''
            stage_space = json.loads(execute(member, script, manifest, 600))
            missing = stage_space['missing']
            if sum((Path(source['lean_path'])/n).stat().st_size for n in missing)+512*1024**2>stage_space['free']:
                raise ValueError('ARRIVAL_SOURCE_DISK_RESERVE:'+member)
            save(home/('space-'+member+'.json'),stage_space)
            save(home/('transfer-'+member+'.json'), dict(files=len(missing), bytes=sum((Path(source['lean_path'])/n).stat().st_size for n in missing)))
            if missing:
                archive = home/('transfer-'+member+'.tar')
                with tarfile.open(archive, 'w') as tar:
                    for name in missing: tar.add((Path(source['lean_path'])/name).resolve(), arcname=name, recursive=False)
                receiver = f'''import hashlib,sys,tarfile
from pathlib import Path
lib=Path({root!r})/'lib';inventory={inventory!r};tar=tarfile.open(fileobj=sys.stdin.buffer,mode='r|');count=0
for item in tar:
 if not item.isfile() or item.name not in inventory:raise ValueError('PRODUCTIVE_ARCHIVE_SCOPE')
 p=lib/item.name;p.parent.mkdir(parents=True,exist_ok=True);temporary=p.with_name(p.name+'.incoming')
 with temporary.open('wb') as out:
  stream=tar.extractfile(item)
  while True:
   data=stream.read(1048576)
   if not data:break
   out.write(data)
 if hashlib.sha256(temporary.read_bytes()).hexdigest()!=inventory[item.name]:raise ValueError('PRODUCTIVE_ARTIFACT_HASH')
 temporary.replace(p);count+=1
print(count)
'''
                receiver_path = root+'/receive.py'
                execute(member, 'from pathlib import Path\nPath('+repr(receiver_path)+').write_text('+repr(receiver)+')', manifest, 60)
                node = roll.spare.transport.node(member)
                with archive.open('rb') as stream:
                    result = node._run_remote(node.remote_argv(item['python'], receiver_path), allow_probe=False,
                        stdin=stream, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900)
                if result.returncode or int(result.stdout) != len(missing): raise RuntimeError('PRODUCTIVE_TRANSFER:'+result.stderr.decode()[-1000:])
                archive.unlink()
                execute(member, 'from pathlib import Path\nPath('+repr(receiver_path)+').unlink()', manifest, 60)
            exporter = ROOT/'Lean/scripts/verification/public-arrival-network-source.lean'
            files = {'closure.json':Path(source['closure']).read_bytes(), 'scripts/verification/'+exporter.name:exporter.read_bytes()}
            execute(member, 'import base64\nfrom pathlib import Path\n'+
                '\n'.join('p=Path('+repr(root+'/'+name)+');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode('+repr(base64.b64encode(raw).decode())+'))' for name,raw in files.items()), manifest, 120)
            tool = cfg['semantic']['backend'][0]
            settings = dict(descriptor=source['descriptor'], exporter=root+'/scripts/verification/'+exporter.name,
                closure=root+'/closure.json', lean_path=root+'/lib', cwd=root, error_log=root+'/source.log',
                backend=[tool,'--trust=0','-j1','--run',root+'/scripts/verification/'+exporter.name,
                         'private-one'], native_call_seconds=300)
        cfg['arrival'] = settings; cfg['semantic']['governance_context'] = context(cfg, manifest['source'])
        cfg['semantic']['replay_seconds'] = 300
        candidate = root+'/arrival-candidate.json'
        script = 'import json,sys,hashlib\nfrom pathlib import Path\nsys.path.insert(0,'+repr(code)+')\nfrom source_semantics import Engine\nc='+repr(cfg)+'\nEngine(c["arrival"])\nPath('+repr(candidate)+').write_text(json.dumps(c,sort_keys=True)+"\\n")\nprint(hashlib.sha256(Path('+repr(tool)+').read_bytes()).hexdigest())'
        compiler_hash = execute(member, script, manifest, 300).strip()
        entry = dict(config=cfg, candidate=candidate, root=root, code=code, compiler_sha256=compiler_hash)
        save(receipt, dict(revision=revision, entry=entry, descriptor=source['descriptor'],
                           original_prefix=original['prefix'], original_digest=original['digest']))
        print('ARRIVAL SOURCE STAGED',member,flush=True)
        return member,entry

    with ThreadPoolExecutor(max_workers=4) as pool: nodes = dict(pool.map(stage, 'abcd'))
    prepared = dict(revision=revision, protocol=protocol, nodes=nodes, descriptor=source['descriptor'],
                    original_prefix=original['prefix'], original_digest=original['digest'])
    prepared_path = home/'prepared.json'
    if prepared_path.exists() and load(prepared_path) != prepared:
        raise ValueError('ARRIVAL_PREPARED_RECEIPT_CHANGED')
    if not prepared_path.exists(): save(prepared_path, prepared)


def readiness(box):
    home = location(box); prepared = load(home/'prepared.json'); manifest = load(home/'online-before.json')
    expected_prefix = prepared['original_prefix']
    def attest(member):
        path=home/('ready-'+member+'.json')
        entry=prepared['nodes'][member]; evidence=entry['root']+'/arrival-readiness'; check=entry['root']+'/arrival-independent'
        if path.exists():
            value=load(path)
            if (value.get('descriptor') != prepared['descriptor']
                    or value.get('revision') != prepared['revision']
                    or value.get('original_digest') != prepared['original_digest']
                    or value.get('acceptance',{}).get('exit') != 0
                    or value.get('acceptance',{}).get('prefix') != expected_prefix
                    or value.get('vote',{}).get('member') != member):
                raise ValueError('ARRIVAL_READY_RECEIPT_CHANGED:'+member)
            return value['vote']
        script=f'''import json,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
import arrival_readiness as p
c=json.loads(Path({entry['candidate']!r}).read_text());e=Path({evidence!r});q=Path({check!r})
if not (e/'vote.json').exists():p.issue(c,e)
if not (q/'acceptance.json').exists():p.check(c,e,q)
print(json.dumps(dict(vote=json.loads((e/'vote.json').read_text()),acceptance=json.loads((q/'acceptance.json').read_text()),evidence=str(e),independent=str(q))))
'''
        value=json.loads(execute(member,script,manifest,1600))
        if (value.get('acceptance',{}).get('exit') != 0
                or value.get('acceptance',{}).get('prefix') != expected_prefix):
            raise ValueError('ARRIVAL_READINESS_PREFIX:'+member)
        value.update(descriptor=prepared['descriptor'],revision=prepared['revision'],
                     original_digest=prepared['original_digest'])
        save(path,value)
        print('INDEPENDENT ARRIVAL READINESS PASS',member,value['acceptance']['prefix']['seq'],flush=True)
        return value['vote']
    with ThreadPoolExecutor(max_workers=4) as pool: votes=list(pool.map(attest,'abcd'))
    certificate=dict(point=votes[0]['receipt']['body']['point'],votes=votes)
    arrival_extension.admission(prepared['nodes']['a']['config'],certificate)
    receipt=dict(certificate=certificate,descriptor=prepared['descriptor'],revision=prepared['revision'],
                 original_prefix=prepared['original_prefix'],original_digest=prepared['original_digest'])
    admission_path=home/'admission.json'
    if admission_path.exists() and load(admission_path) != receipt:
        raise ValueError('ARRIVAL_ADMISSION_RECEIPT_CHANGED')
    if not admission_path.exists(): save(admission_path,receipt)


def install(box):
    home=location(box);lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    prepared=load(home/'prepared.json');before=load(home/'online-before.json')
    admission=load(home/'admission.json');certificate=admission['certificate']
    original=load(home/'original-before.json')
    if (admission.get('descriptor') != prepared['descriptor']
            or admission.get('revision') != prepared['revision']
            or admission.get('original_prefix') != original['prefix']
            or admission.get('original_digest') != original['digest']
            or prepared.get('original_prefix') != original['prefix']
            or prepared.get('original_digest') != original['digest']):
        raise ValueError('ARRIVAL_PREPARE_BINDING')
    if prepared['protocol']!={n:sha(NETWORK/n) for n in prepared['protocol']}:raise ValueError('ARRIVAL_CODE_CHANGED')
    literal=[list(row) for row in roll.spare.rows(before['mac']['service']['database'])]
    if literal != original['rows'] or len(literal) != 68:raise ValueError('ARRIVAL_ORIGINAL_PREFIX_MOVED')
    productive_extension.require(before['mac']['service'], literal)
    if (home/'installed.json').exists():
        current=load(box/'ha/deployment.json')
        receipt=load(home/'installed.json')
        if (current.get('arrival',{}).get('admission')!=digest(certificate)
                or receipt.get('prefix') != original['prefix']
                or receipt.get('original_digest') != original['digest']
                or literal != original['rows']):raise ValueError('ARRIVAL_INSTALL_CHANGED')
        print('PAID ARRIVAL INSTALL RETAINED',flush=True);return
    manifest=copy.deepcopy(before);prefix=certificate['point']['prefix']
    if prefix != original['prefix']:raise ValueError('ARRIVAL_PARENT_MOVED')
    progress_path=home/'install-progress.json'
    progress=load(progress_path) if progress_path.exists() else {'stages':[], 'prefix':prefix, 'original_digest':original['digest']}
    if progress.get('prefix') != prefix or progress.get('original_digest') != original['digest']:
        raise ValueError('ARRIVAL_PROGRESS_BINDING')
    def paid(stage):
        if stage not in progress['stages']:progress['stages'].append(stage)
        save(progress_path,progress);print('ARRIVAL ROLL',stage,flush=True)
    configs={};services={}
    for member,entry in prepared['nodes'].items():
        cfg=copy.deepcopy(entry['config']);cfg['arrival_extension']=certificate
        cfg['semantic']['governance_context']=context(cfg,manifest['source']);arrival_extension.admission(cfg);configs[member]=cfg
        if member!='a':manifest['nodes'][member].update(code=entry['code'],protocol=prepared['protocol'])
    inventory=load(prepared['nodes']['a']['config']['arrival']['closure'])
    for owner,member in [('mac','a'),('spark','c')]:
        cfg=copy.deepcopy(before[owner]['service']);entry=prepared['nodes'][member]
        cfg.update(arrival=configs[member]['arrival'],arrival_extension=certificate)
        settings=cfg['arrival'];worker=dict(command=[settings['backend'][0],'--trust=0','-j1','-DElab.async=false',
            '-DwarningAsError=true','--run','scripts/verification/public-arrival-network-source.lean','public'],
            cwd=settings['cwd'],lean_path=settings['lean_path'],stderr=entry['root']+'/public-worker.stderr',
            compiler_sha256=entry['compiler_sha256'],contract='original-source-arrival-public/v1',timeout=300)
        inputs={settings['exporter']:settings['descriptor']['exporter_sha256'],settings['closure']:settings['descriptor']['closure_sha256']}
        inputs.update({settings['lean_path']+'/'+n:w for n,w in inventory.items()})
        inputs={**cfg['online_privacy'].get('source_inputs',{}),**inputs}
        cfg['online_privacy']={**cfg['online_privacy'],'worker':worker,'source_inputs':inputs};services[owner]=cfg
    if 'writer-barrier' not in progress['stages'] or (home/'install-failed.json').exists():
        frozen={}
        try:
            for owner in ('spark','mac'):
                frozen[owner]=roll.freeze_writer(box,before,owner);save(home/'writer-barrier.json',frozen)
            from ha_quorum import Quorum
            end=time.monotonic()+30
            while True:
                states=Quorum(before['mac']['service']).collect('status')
                if set(states)==set('abcd') and all(not v['intents'] and {k:v['head'][k] for k in ('seq','head')}==prefix for v in states.values()):break
                if time.monotonic()>=end:raise ValueError('ARRIVAL_ROLL_BARRIER')
                time.sleep(.5)
            save(home/'barrier-status.json',states);paid('writer-barrier')
            failed=home/'install-failed.json'
            if failed.exists():failed.rename(home/('install-failed-'+str(time.time_ns())+'.json'))
        except BaseException:
            for owner,record in frozen.items():roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            raise
    frozen=load(home/'writer-barrier.json')
    try:
        from ha_quorum import Quorum
        for member in 'bcd':
            if 'anchor-'+member in progress['stages']:continue
            item=manifest['nodes'][member]
            command=[item['python'],item['code']+'/live_timing.py','host',item['home']]
            inspect=f'''import json,shlex,subprocess
from pathlib import Path
want={command!r};found=[]
for row in subprocess.check_output(['ps','-axo','pid=,command='],text=True).splitlines():
 try:
  pid,argv=row.strip().split(None,1)
  if shlex.split(argv)==want:found.append(int(pid))
 except ValueError:pass
assert len(found)<=1,'ARRIVAL_DUPLICATE_ANCHOR_HOST'
same=json.loads(Path({item['home']+'/config.json'!r}).read_text())=={configs[member]!r}
print(json.dumps(dict(pids=found,same_config=same)))
'''
            running=json.loads(execute(member,inspect,manifest,60))
            if not running['pids'] or not running['same_config']:
                execute(member,'from pathlib import Path\nPath('+repr(item['home']+'/config.json')+').write_text('+repr(json.dumps(configs[member])+'\n')+')',manifest,90)
                roll.restart_anchor(member,manifest)
            else:print('PAID ARRIVAL ANCHOR START RETAINED',member,flush=True)
            save(home/('anchor-started-'+member+'.json'),dict(release=prepared['revision'],configuration=digest(configs[member]),observed=running))
            client=Quorum(before['mac']['service']).nodes[member]
            try:remaining=max(0,len(literal)-client.call('semantic-status')['prefix']['seq'])
            except (ValueError,OSError,EOFError):remaining=len(literal)
            # The cold journal pays each unvisited source call; observing it
            # must not restart an interpreter that is still consuming that word.
            seconds=configs[member]['arrival'].get('native_call_seconds',300)
            end=time.monotonic()+max(360,(remaining+2)*seconds)
            while time.monotonic()<end:
                try:
                    state=client.call('semantic-status')
                    if state['prefix']==prefix and state['backend'] and not state['warm_error']:break
                except (ValueError,OSError,EOFError):pass
                time.sleep(2)
            else:raise TimeoutError('ARRIVAL_VOTER_NOT_READY:'+member)
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
                roll.module('arrival_stop','public-recovery-isolation.py').stop(box)
                save(box/'ha/mac/service.json',services[owner]);save(box/'ha/mac/controller.json',manifest[owner]['controller'])
                (box/'runtime/STOP').unlink(missing_ok=True)
                subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            paid('candidate-'+owner)
        manifest.update(protocol=prepared['protocol'],release=prepared['revision'],arrival=dict(descriptor=prepared['descriptor'],evidence=str(home),admission=digest(certificate)))
        manifest['public_timing']['release']=prepared['revision']
        manifest['application_receipts']['protocol']=prepared['protocol']
        for owner,member in [('mac','a'),('spark','c')]:manifest['application_receipts']['candidates'][owner]['code']=prepared['nodes'][member]['code']
        for member in 'abcd':manifest['semantic']['configurations'][member]=configs[member]['semantic']
        save(box/'ha/deployment.json',manifest)
        if [list(row) for row in roll.spare.rows(manifest['mac']['service']['database'])]!=literal:raise ValueError('ARRIVAL_ROLL_CHANGED_JOURNAL')
        save(home/'installed.json',dict(prefix=prefix,release=prepared['revision'],admission=digest(certificate),
            original_digest=original['digest'],original_admission=digest(before['native_admission']),
            productive_admission=digest(before.get('productive',{}).get('admission','')),stages=progress['stages'],activated=False))
        print('ARRIVAL SOURCE INSTALLED: original 68-event journal unchanged; control event required',flush=True)
    except BaseException:
        save(home/'install-failed.json',dict(at=time.time(),stages=progress['stages'],prefix=prefix,original_digest=original['digest']))
        for owner,record in frozen.items():
            try:roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            except (OSError,ValueError,RuntimeError,subprocess.SubprocessError):pass
        raise


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('operation',choices=['prepare','readiness','install']);p.add_argument('box',type=Path);a=p.parse_args()
    globals()[a.operation.replace('-','_')](a.box.resolve())
