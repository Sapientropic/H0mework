"""Stage, attest and roll a journal-admitted supply source on the existing four nodes."""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
import copy
import errno
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT / 'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from crypto import canonical, digest
from recovery_loop import save
from source_semantics import Engine
import source_extension


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value


roll = module('supply_roll', 'public-live-timing.py')
load, sha, execute = roll.load, roll.sha, roll.execute


def location(box):
    return box / 'ha/regeneration/online'


def same_file(path, raw):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        if path.read_bytes() != raw: raise ValueError('IMMUTABLE_STAGE_CHANGED:' + str(path))
    else:
        with path.open('xb') as stream: stream.write(raw)


def context(config, source):
    names = ('registry', 'ha', 'semantic_policy', 'governance', 'energy', 'continuation',
             'handoff', 'regeneration', 'native_admission', 'governance_members', 'cluster')
    value = {name: copy.deepcopy(config[name]) for name in names}
    value.update(source=source, stream='recovery', semantic={'descriptor': config['semantic']['descriptor']})
    if 'source_extension' in config: value['source_extension'] = config['source_extension']
    return value


def retire_writer(box, manifest, owner, record):
    checked=copy.deepcopy(record)
    # A child that exited between ps and birth has no live occurrence to retire.
    checked['observed_processes']=[p for p in checked.get('observed_processes',[]) if p['birth']]
    roll.retire_writer(box,manifest,owner,checked)


def prepare(box, bundle):
    home = location(box); home.mkdir(parents=True, exist_ok=True)
    manifest = load(box/'ha/deployment.json'); source = load(bundle/'candidate.json')['regeneration']
    if source['descriptor']['exporter_sha256'] != sha(ROOT/'Lean/scripts/verification/public-supply-network-source.lean'):
        raise ValueError('PAID_SOURCE_CHANGED')
    Engine(source)
    names = sorted(set(manifest['protocol']) | {'source_extension.py', 'regeneration.py', 'client.py',
                    'source_readiness.py', 'source_readiness_check.py'})
    protocol = {name: sha(NETWORK/name) for name in names}; revision = digest(protocol)
    configs, candidates, compiler_hashes = {}, {}, {}
    inventory = load(source['closure']); local_root = Path(source['lean_path'])
    total = sum((local_root/name).stat().st_size for name in inventory)
    plan = load(home/'resource-plan.json')
    plan.update(source_view_logical_bytes=total, source_view_peak_bytes_per_node=total+1024**3,
                phase='reuse-paid-transitive-source-and-four-local-votes', transfer='missing content hashes only')
    save(home/'resource-plan.json', plan)
    if not (home/'before.json').exists(): save(home/'before.json', manifest)
    for member in 'abcd':
        path = home/('anchor-before-'+member+'.json')
        if path.exists(): config = load(path)
        elif member == 'a':
            config = load(box/'local-anchor/config.json'); save(path, config)
        else:
            item = manifest['nodes'][member]
            config = json.loads(execute(member, 'from pathlib import Path\nprint(Path('+repr(item['home']+'/config.json')+').read_text())', manifest, 60))
            save(path, config)
        configs[member] = config
    exporter = ROOT/'Lean/scripts/verification/public-supply-network-source.lean'

    def stage(member):
        receipt=home/('staged-'+member+'.json')
        if receipt.exists():
            prior=load(receipt)
            if prior['revision']==revision and prior['entry']['config']['regeneration']['descriptor']==source['descriptor']:
                return member,prior['entry']
        config = copy.deepcopy(configs[member]); tool = config['semantic']['backend'][0]
        if member == 'a':
            native = home/'native-closed'; native.mkdir(exist_ok=True)
            lib = native/'lib'; lib.mkdir(exist_ok=True)
            for name, wanted in inventory.items():
                target = lib/name
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    try:os.link((local_root/name).resolve(strict=True), target)
                    except OSError as error:
                        if error.errno != errno.EXDEV:raise
                        shutil.copyfile((local_root/name).resolve(strict=True), target)
            same_file(native/'closure.json', Path(source['closure']).read_bytes())
            same_file(native/'scripts/verification'/exporter.name, exporter.read_bytes())
            root = str(native); codepath = str(NETWORK); compiler_hash = sha(tool)
            transferred = 0
        else:
            item = manifest['nodes'][member]
            root = item['home']+'/regeneration/source-'+digest(source['descriptor'])
            release = item['home']+'/code/'+revision
            codepath = release+'/Verification/public-audit/network'
            payload = {n: base64.b64encode((NETWORK/n).read_bytes()).decode() for n in names}
            roots = [config[n]['lean_path'] for n in ('semantic','governance','energy','continuation','handoff')]
            node = roll.spare.transport.node(member)
            code = f'''import base64,errno,hashlib,json,os,shutil
from pathlib import Path
root=Path({root!r});lib=root/'lib';lib.mkdir(parents=True,exist_ok=True)
inventory={inventory!r};roots={roots!r};cas=Path({node.c.remote_home!r})/'cas'
(root/'transfer-inventory.json').write_text(json.dumps(inventory))
missing=[];reused=0
for name,wanted in inventory.items():
 target=lib/name
 if target.exists():
  assert hashlib.sha256(target.read_bytes()).hexdigest()==wanted
  continue
 candidates=[cas/wanted[:2]/wanted]+[Path(p)/name for p in roots]
 origin=next((p for p in candidates if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==wanted),None)
 if origin is None:missing.append(name)
 else:
  target.parent.mkdir(parents=True,exist_ok=True)
  try:os.link(origin,target)
  except OSError as error:
   if error.errno!=errno.EXDEV:raise
   shutil.copyfile(origin,target)
  reused+=1
for n,v in {payload!r}.items():
 p=Path({codepath!r})/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v)
 assert hashlib.sha256(raw).hexdigest()=={protocol!r}[n]
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
p=Path({release!r})/'Lean/scripts/verification/{exporter.name}';p.parent.mkdir(parents=True,exist_ok=True)
raw=base64.b64decode({base64.b64encode(exporter.read_bytes()).decode()!r})
if p.exists():assert p.read_bytes()==raw
else:p.write_bytes(raw)
print(json.dumps(dict(missing=missing,reused=reused,compiler_sha256=hashlib.sha256(Path({tool!r}).read_bytes()).hexdigest())))
'''
            inspected = json.loads(execute(member, code, manifest, 240))
            missing = inspected['missing']; transferred = sum((local_root/n).stat().st_size for n in missing)
            save(home/('transfer-'+member+'.json'), dict(files=len(missing), bytes=transferred, reused=inspected['reused']))
            archive = home/('transfer-'+member+'.tar')
            if missing:
                reusable = False
                if archive.exists():
                    with tarfile.open(archive, 'r') as tar:
                        members = tar.getmembers()
                        reusable = [m.name for m in members] == missing and all(
                            m.isfile() and m.size == (local_root/m.name).stat().st_size for m in members)
                if not reusable:
                    with tarfile.open(archive, 'w') as tar:
                        for name in missing: tar.add((local_root/name).resolve(strict=True), arcname=name, recursive=False)
                # Only regular, named members from this exact immutable inventory are accepted.
                unpack = f'''import hashlib,json,os,sys,tarfile
from pathlib import Path,PurePosixPath
root=Path({root!r});lib=root/'lib';inventory=json.loads((root/'transfer-inventory.json').read_text());count=0
tar=tarfile.open(fileobj=sys.stdin.buffer,mode='r|')
for item in tar:
 if not item.isfile() or item.name not in inventory or PurePosixPath(item.name).is_absolute() or '..' in PurePosixPath(item.name).parts:raise ValueError('SOURCE_ARCHIVE_SCOPE')
 target=lib/item.name;target.parent.mkdir(parents=True,exist_ok=True);temporary=target.with_name(target.name+'.incoming')
 with temporary.open('wb') as out:
  stream=tar.extractfile(item)
  while True:
   block=stream.read(1048576)
   if not block:break
   out.write(block)
 assert hashlib.sha256(temporary.read_bytes()).hexdigest()==inventory[item.name]
 if target.exists():
  assert hashlib.sha256(target.read_bytes()).hexdigest()==inventory[item.name];temporary.unlink()
 else:temporary.rename(target)
 count+=1
print(json.dumps(dict(received=count)))
'''
                receiver = root+'/receive-source.py'
                execute(member, 'from pathlib import Path\nPath('+repr(receiver)+').write_text('+repr(unpack)+')', manifest, 60)
                # stdin carries the archive, not shell text or a command string.
                with archive.open('rb') as stream:
                    result = node._run_remote(node.remote_argv(item['python'], receiver),
                        allow_probe=False, stdin=stream, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=1200)
                if result.returncode: raise RuntimeError(result.stderr.decode()[-1000:])
                if json.loads(result.stdout)['received'] != len(missing): raise ValueError('SOURCE_ARCHIVE_COUNT')
                archive.unlink()
                execute(member, 'from pathlib import Path\nPath('+repr(receiver)+').unlink()', manifest, 60)
            raw = {'closure.json': base64.b64encode(Path(source['closure']).read_bytes()).decode(),
                   'scripts/verification/'+exporter.name: base64.b64encode(exporter.read_bytes()).decode()}
            finish = f'''import base64,json
from pathlib import Path
root=Path({root!r})
for n,v in {raw!r}.items():
 p=root/n;p.parent.mkdir(parents=True,exist_ok=True);b=base64.b64decode(v)
 if p.exists():assert p.read_bytes()==b
 else:p.write_bytes(b)
(root/'transfer-inventory.json').unlink(missing_ok=True)
print('SOURCE_BYTES_STAGED')
'''
            execute(member, finish, manifest, 120)
            compiler_hash = inspected['compiler_sha256']
        settings = dict(descriptor=source['descriptor'], exporter=root+'/scripts/verification/'+exporter.name,
            closure=root+'/closure.json', lean_path=root+'/lib', cwd=root, error_log=root+'/source.log',
            backend=[tool,'--trust=0','-j1','--run',root+'/scripts/verification/'+exporter.name,'private-one'],
            native_call_seconds=180)
        config['regeneration'] = settings
        config['semantic']['governance_context'] = context(config, manifest['source'])
        config['semantic']['replay_seconds'] = 300
        candidate = root+'/candidate.json'
        code = f'''import json,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from source_semantics import Engine
c={config!r};Engine(c['regeneration']);p=Path({candidate!r})
raw=json.dumps(c,sort_keys=True)+'\\n'
if p.exists():assert p.read_text()==raw
else:p.write_text(raw)
print('EXACT_SOURCE_VIEW_PASS')
'''
        execute(member, code, manifest, 240)
        save(home/('candidate-'+member+'.json'), config)
        print('SUPPLY SOURCE STAGED', member, 'new bytes', transferred, flush=True)
        entry=dict(config=config, candidate=candidate, code=codepath, root=root, compiler_sha256=compiler_hash)
        save(receipt,dict(revision=revision,entry=entry))
        return member,entry

    def checked_stage(member):
        try:return stage(member)
        except Exception as error:
            save(home/('stage-failed-'+member+'.json'),dict(error=type(error).__name__,detail=str(error),at=time.time()))
            print('SOURCE STAGE NEEDS REPAIR',member,type(error).__name__,str(error)[-300:],flush=True)
            return member,None
    with ThreadPoolExecutor(max_workers=3) as pool:
        staged = dict(pool.map(checked_stage, 'abcd'))
    if any(value is None for value in staged.values()):raise ValueError('SOURCE_STAGE_INCOMPLETE')
    save(home/'prepared.json', dict(descriptor=source['descriptor'], protocol=protocol, revision=revision, nodes=staged,
                                  bundle=str(bundle), source_view_bytes=total))


def readiness(box, paid_a=None):
    home = location(box); prepared = load(home/'prepared.json'); manifest = load(home/'before.json')
    def attest(member):
        entry = prepared['nodes'][member]; root = entry['root']; codepath = entry['code']
        evidence, check = root+'/readiness', root+'/independent'
        if member == 'a' and paid_a:
            prior = Path(paid_a)
            if not Path(evidence).exists(): Path(evidence).symlink_to(prior/'issued-a-closed', target_is_directory=True)
            if not Path(check).exists(): Path(check).symlink_to(prior/'independent-a', target_is_directory=True)
        code = f'''import json,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
import source_readiness as p,source_readiness_check as v
c=json.loads(Path({entry['candidate']!r}).read_text());e=Path({evidence!r});q=Path({check!r})
if not (e/'vote.json').exists():p.issue(c,e)
if not (q/'acceptance.json').exists():v.check(c,e,q)
member,rows,prefix=p.snapshot(c)
vote=json.loads((e/'vote.json').read_text());argument=json.loads((e/'input.json').read_text());result=json.loads((e/'output.json').read_text())
v.consume(c,[list(r) for r in rows],prefix,vote,argument,result)
print(json.dumps(dict(vote=vote,acceptance=json.loads((q/'acceptance.json').read_text()),evidence=str(e),independent=str(q))))
'''
        value = json.loads(execute(member, code, manifest, 1100))
        save(home/('ready-'+member+'.json'), value)
        print('INDEPENDENT SUPPLY READINESS PASS', member, value['acceptance']['prefix']['seq'], flush=True)
        return value['vote']
    with ThreadPoolExecutor(max_workers=4) as pool:
        votes = list(pool.map(attest, 'abcd'))
    certificate = dict(point=votes[0]['receipt']['body']['point'], votes=votes)
    source_extension.admission(prepared['nodes']['a']['config'], certificate)
    save(home/'admission.json', certificate)
    print('FOUR SOURCE VOTES ACCEPTED: original certificate unchanged; activation not yet committed', flush=True)


def install(box):
    lock=(box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home = location(box); prepared = load(home/'prepared.json'); before = load(home/'before.json')
    certificate = load(home/'admission.json'); manifest = copy.deepcopy(before)
    if prepared['protocol'] != {n: sha(NETWORK/n) for n in prepared['protocol']}:
        raise ValueError('STAGED_PROTOCOL_CHANGED')
    if (home/'installed.json').exists():
        current=load(box/'ha/deployment.json');installed=load(home/'installed.json')
        assert installed['release']==current['release']==prepared['revision']
        assert installed['admission']==current['regeneration']['admission']==digest(certificate)
        assert current['native_admission']==before['native_admission']
        active=source_extension.committed(current['mac']['service'],roll.spare.rows(current['mac']['service']['database']))
        if active is not None:assert active[1]==certificate
        print('PAID SUPPLY INSTALL RETAINED: no restart, rewrite or append; journal activation='+str(active[0] if active else None),flush=True)
        return
    prefix = certificate['point']['prefix']
    literal = roll.spare.rows(before['mac']['service']['database'])
    if dict(seq=len(literal), head=literal[-1][2]) != prefix:
        raise ValueError('READINESS_PARENT_MOVED')
    progress = load(home/'install-progress.json') if (home/'install-progress.json').exists() else {'stages':[]}
    def paid(stage):
        if stage not in progress['stages']: progress['stages'].append(stage)
        save(home/'install-progress.json', progress)
        print('SUPPLY ROLL', stage, flush=True)
    configs = {}
    for member, entry in prepared['nodes'].items():
        cfg = copy.deepcopy(entry['config']); cfg['source_extension'] = certificate
        cfg['semantic']['governance_context'] = context(cfg, manifest['source'])
        source_extension.admission(cfg); configs[member] = cfg
        if member != 'a':
            manifest['nodes'][member].update(code=entry['code'],protocol=prepared['protocol'])
    services = {}
    for owner, member in [('mac','a'),('spark','c')]:
        cfg = copy.deepcopy(before[owner]['service']); entry = prepared['nodes'][member]
        cfg.update(regeneration=configs[member]['regeneration'], native_admission=before['native_admission'],
                   cluster=digest(before['trust']), source_extension=certificate)
        settings = cfg['regeneration']; script = settings['exporter']
        worker = dict(command=[settings['backend'][0], '--trust=0','-j1','-DElab.async=false',
            '-DwarningAsError=true','--run','scripts/verification/public-supply-network-source.lean','public'],
            cwd=settings['cwd'], lean_path=settings['lean_path'], stderr=entry['root']+'/public-worker.stderr',
            compiler_sha256=entry['compiler_sha256'], contract='complete-default-supply-privacy/v1', timeout=180)
        inputs = {script: settings['descriptor']['exporter_sha256'],
                  settings['closure']: settings['descriptor']['closure_sha256']}
        inputs.update({settings['lean_path']+'/'+n: wanted for n,wanted in load(Path(prepared['nodes']['a']['config']['regeneration']['closure'])).items()})
        cfg['online_privacy'] = {**cfg['online_privacy'], 'worker':worker,'source_inputs':inputs}
        services[owner] = cfg
    if 'writer-barrier' not in progress['stages']:
        frozen = {}
        try:
            for owner in ('spark','mac'):
                frozen[owner] = roll.freeze_writer(box, before, owner)
                save(home/'writer-barrier.json', frozen)
            from ha_quorum import Quorum
            end=time.monotonic()+30
            while True:
                states = Quorum(before['mac']['service']).collect('status')
                if set(states)==set('abcd') and all(not v['intents'] and
                        {k:v['head'][k] for k in ('seq','head')} == prefix for v in states.values()):break
                if time.monotonic()>=end:
                    save(home/'barrier-incomplete.json',dict(expected=prefix,states=states))
                    raise ValueError('SUPPLY_ROLL_BARRIER')
                time.sleep(.5)
            save(home/'barrier-status.json', states); paid('writer-barrier')
        except BaseException:
            for owner,record in frozen.items(): roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            raise
    frozen = load(home/'writer-barrier.json')
    try:
        from ha_quorum import Quorum
        for member in 'bcd':
            if 'anchor-'+member in progress['stages']: continue
            item = manifest['nodes'][member]
            execute(member, 'from pathlib import Path\nPath('+repr(item['home']+'/config.json')+').write_text('+repr(json.dumps(configs[member])+'\n')+')', manifest, 90)
            roll.restart_anchor(member,manifest)
            end = time.monotonic()+360; client = Quorum(before['mac']['service']).nodes[member]
            while time.monotonic()<end:
                try:
                    state = client.call('semantic-status')
                    if state['prefix']==prefix and state['backend'] and not state['warm_error']:break
                except (ValueError,OSError,EOFError):pass
                time.sleep(2)
            else:raise TimeoutError('SUPPLY_ROLL_VOTER_NOT_READY:'+member)
            paid('anchor-'+member)
        save(box/'local-anchor/config.json',configs['a'])
        for owner in ('mac','spark'):
            manifest[owner]['service'] = services[owner]
            manifest[owner]['controller']['release'] = prepared['revision']
        for owner in ('spark','mac'):
            if 'candidate-'+owner in progress['stages']:continue
            retire_writer(box,before,owner,frozen[owner])
            if owner=='spark':
                item=manifest['nodes']['c'];command=[item['python'],item['code']+'/live_timing.py','coordinator',item['home']+'/ha/controller.json']
                code=f'''import json
from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'runtime/STOP').unlink(missing_ok=True)
(p/'service.json').write_text({json.dumps(services[owner])!r}+'\\n')
(p/'controller.json').write_text({json.dumps(manifest[owner]['controller'])!r}+'\\n')
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
'''
                execute('c',code,manifest,60)
                roll.spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
            else:
                roll.module('supply_stop','public-recovery-isolation.py').stop(box)
                save(box/'ha/mac/service.json',services[owner]);save(box/'ha/mac/controller.json',manifest[owner]['controller'])
                (box/'runtime/STOP').unlink(missing_ok=True)
                subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                    sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            paid('candidate-'+owner)
        manifest.update(protocol=prepared['protocol'],release=prepared['revision'],regeneration={
            'descriptor':prepared['descriptor'],'configurations':{n:v['config']['regeneration'] for n,v in prepared['nodes'].items()},
            'evidence':str(home),'admission':digest(certificate)})
        manifest['public_timing']['release']=prepared['revision']
        for member in 'abcd': manifest['semantic']['configurations'][member]=configs[member]['semantic']
        save(box/'ha/deployment.json',manifest)
        if roll.spare.rows(manifest['mac']['service']['database'])!=literal:raise ValueError('ROLL_CHANGED_JOURNAL')
        save(home/'installed.json',dict(prefix=prefix,release=prepared['revision'],admission=digest(certificate),
            original_admission=digest(before['native_admission']),stages=progress['stages'],activated=False))
        print('SUPPLY SOURCE INSTALLED: journal unchanged; actual control event still required',flush=True)
    except BaseException:
        # Before any control event the old configs remain a lawful fallback.
        # Preserve the exact paid stage and restore both writers, not the DBs.
        save(home/'install-failed.json',dict(at=time.time(),stages=progress['stages']))
        for owner,record in frozen.items():
            try:roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            except (OSError,ValueError,RuntimeError,subprocess.SubprocessError):pass
        raise


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path); parser.add_argument('phase', choices=('prepare','readiness','install'))
    parser.add_argument('--bundle', type=Path); parser.add_argument('--paid-a', type=Path)
    args = parser.parse_args()
    if args.phase == 'prepare': prepare(args.box.resolve(), args.bundle.resolve())
    elif args.phase=='readiness': readiness(args.box.resolve(), args.paid_a)
    else:install(args.box.resolve())
