"""Roll the original two candidates/four admitted verifiers onto public timing."""
import argparse
import base64
import copy
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from crypto import digest
from ha_quorum import Quorum
from recovery_loop import save


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


spare = module('timing_rollout_transport', 'public-native-spare.py')
load = spare.load


def execute(member, code, manifest, timeout=180):
    compile(code, '<owned-node-script>', 'exec')
    return spare.execute(member, code, manifest, timeout)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def freeze_writer(box, manifest, owner):
    member = 'a' if owner == 'mac' else 'c'
    state = str(box/'runtime') if member == 'a' else manifest['nodes'][member]['home']+'/ha/runtime'
    codepath = str(NETWORK) if member == 'a' else manifest['nodes'][member]['code']
    code = f'''import json,os,signal,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from anchor import public_key
from crypto import verify
p=Path({state!r});v=verify(public_key({manifest['owners'][owner]!r}),'ha-coordinator',json.loads((p/'ha-status.json').read_text()))
assert v['owner']=={owner!r} and v['source']=={manifest['source']!r}
assert v['boot']==boot_identity() and birth(v['pid'])==v['birth']
os.kill(v['pid'],signal.SIGSTOP)
try:
 r=json.loads((p/'ha-service-process.json').read_text()) if (p/'ha-service-process.json').exists() else None
 if r and r['boot']==boot_identity() and birth(r['pid'])==r['birth']:
  assert r['pgid']==r['pid']==os.getpgid(r['pid'])
  assert r['argv'][-1]==str(p/'ha-service.json')
  os.killpg(r['pid'],signal.SIGSTOP)
 else:r=None
 v['service']=r
 rows=[]
 for line in __import__('subprocess').check_output(['ps','-axo','pid=,ppid=,uid='],text=True).splitlines():
  a=line.split()
  if len(a)==3:rows.append(tuple(map(int,a)))
 owned={{v['pid']}}
 while True:
  children={{a for a,b,u in rows if b in owned and u==os.getuid()}}
  if children<=owned:break
  owned|=children
 v['observed_processes']=[{{'pid':pid,'birth':birth(pid)}} for pid in owned]
 print(json.dumps(v))
except BaseException:
 os.kill(v['pid'],signal.SIGCONT);raise
'''
    return json.loads(execute(member, code, manifest, 40))


def retire_writer(box, manifest, owner, record):
    spare.retire_writer(box, manifest, owner, record)
    member = 'a' if owner == 'mac' else 'c'
    codepath = str(NETWORK) if member == 'a' else manifest['nodes'][member]['code']
    code = f'''import json,os,signal,sys,time
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
r={record!r};assert r['boot']==boot_identity()
assert birth(r['pid'])!=r['birth']
for p in r.get('observed_processes',[]):
 if p['birth'] and birth(p['pid'])==p['birth']:os.kill(p['pid'],signal.SIGKILL)
end=time.monotonic()+5
while time.monotonic()<end and any(birth(p['pid'])==p['birth'] for p in r.get('observed_processes',[])):time.sleep(.1)
assert all(birth(p['pid'])!=p['birth'] for p in r.get('observed_processes',[]))
print('ORIGINAL_RETIRED_TREE_CLOSED')
'''
    assert execute(member, code, manifest, 15).strip() == 'ORIGINAL_RETIRED_TREE_CLOSED'


def wire_closure(box, manifest):
    cfg = manifest['spark']['service']
    worker = cfg['online_privacy']['worker']
    target = worker['lean_path'].split(':')[0]
    source = cfg['public_base_source']['lean_path']
    code = f'''import json,os,subprocess
from pathlib import Path
p=Path({source!r});q=Path({target!r});count=0
for f in p.rglob('*'):
 if f.is_file():
  t=q/f.relative_to(p);t.parent.mkdir(parents=True,exist_ok=True)
  if not t.exists():os.link(f,t);count+=1
w={worker!r};e=os.environ.copy();e['LEAN_PATH']=w['lean_path']
r=subprocess.run(w['command'],cwd=w['cwd'],env=e,input='',text=True,capture_output=True,timeout=45)
assert r.returncode==0 and not r.stdout and not r.stderr,(r.stdout,r.stderr)
print(json.dumps({{'new_hardlinks':count,'reader_import_exit':r.returncode}}))
'''
    result = json.loads(execute('c', code, manifest, 60))
    save(box/'ha/live-timing/wire-closure.json', result)


def install(box):
    home = box/'ha/live-timing'
    home.mkdir(parents=True, exist_ok=True)
    manifest_path = box/'ha/deployment.json'
    manifest = load(manifest_path)
    if (home/'installed.json').exists():
        assert manifest['public_timing']['release'] == load(home/'installed.json')['release']
        wire_closure(box, manifest)
        print('PUBLIC TIMING ALREADY INSTALLED: retain actual epochs; independently verify', flush=True)
        return
    if not (home/'before.json').exists():
        save(home/'before.json', manifest)
        save(home/'original-events.json', spare.rows(manifest['mac']['service']['database']))
    before = load(home/'before.json')
    literal = load(home/'original-events.json')
    assert len(literal) == 27 and [list(r) for r in spare.rows(before['mac']['service']['database'])] == literal
    progress = load(home/'progress.json') if (home/'progress.json').exists() else {'stages': []}

    def paid(stage):
        if stage not in progress['stages']:
            progress['stages'].append(stage)
        save(home/'progress.json', progress)
        save(manifest_path, manifest)
        print('LIVE PUBLIC TIMING '+stage, flush=True)

    names = sorted(set(before['protocol']) | {'live_timing.py', 'ha_timing.py', 'online_privacy.py', 'privacy_transport.py'})
    protocol = {n: sha(NETWORK/n) for n in names}
    revision = digest(protocol)
    save(home/'resource-plan.json', {'owner': 'process-generated-society', 'consumer': 'default original27/full observation audit',
        'existing_node_states': ['public-anchor-'+n+'-20261102' for n in ('pc', 'spark', 'studio')],
        'new_jobs': 0, 'new_host_reboots': 0, 'extra_mib_per_node': 64,
        'cpu': 'one public Lean reader in the existing source unit limits; no daemon changes'})
    public_lib = box.parent/'privacy/network-accepted-03/lib'
    base_inventory = load(before['semantic']['configurations']['a']['closure'])
    extra = {str(p.relative_to(public_lib)): base64.b64encode(p.read_bytes()).decode()
             for p in public_lib.rglob('*') if p.is_file() and str(p.relative_to(public_lib)) not in base_inventory}
    extra_hash = {n: hashlib.sha256(base64.b64decode(v)).hexdigest() for n, v in extra.items()}
    configs = {}
    for member in 'abcd':
        if member == 'a':
            configs[member] = load(box/'local-anchor/config.json')
        else:
            configs[member] = json.loads(execute(member, 'from pathlib import Path\nprint(Path('+repr(before['nodes'][member]['home']+'/config.json')+').read_text())', before, 40))
        configs[member]['public_representative'] = 'original-fixed-source/v1'
    for member in 'bcd':
        item = before['nodes'][member]
        release = item['home']+'/code/'+revision
        if 'upload-'+member not in progress['stages']:
            payload = {n: base64.b64encode((NETWORK/n).read_bytes()).decode() for n in names}
            code = f'''import base64,hashlib,json,sys
from pathlib import Path
p=Path({release!r});p.mkdir(parents=True,exist_ok=True)
for n,v in {payload!r}.items():
 b=base64.b64decode(v);assert hashlib.sha256(b).hexdigest()=={protocol!r}[n]
 f=p/n
 if f.exists():assert f.read_bytes()==b
 else:f.write_bytes(b)
sys.path.insert(0,str(p))
from live_timing import Journal
from native_spare import admission
from ha_timing import public_configuration
admission({configs[member]!r});public_configuration({configs[member]!r})
print('PUBLIC_ENTRY_IMPORT_AND_ADMISSION_PASS')
'''
            execute(member, code, before, 90)
            paid('upload-'+member)
        manifest['nodes'][member] = {**item, 'code': release, 'protocol': protocol}
    # Wire reuses all existing immutable dependencies; only its small missing
    # module suffix is transferred. Original source descriptors are unchanged.
    service_configs = {}
    prefix = {'seq': 24, 'head': literal[23][2]}
    for owner, member in (('mac', 'a'), ('spark', 'c')):
        cfg = copy.deepcopy(before[owner]['service'])
        base = configs[member]['semantic']
        cfg.update(public_representative='original-fixed-source/v1', public_base_source=base,
                   backend=base['backend'], lean_path=base['lean_path'])
        directory = str(home/owner) if member == 'a' else before['nodes'][member]['home']+'/ha/live-timing'
        worker = {'command': [base['backend'][0], '--trust=0', '-j1', '-DElab.async=false', '-DwarningAsError=true',
                              '--run', 'scripts/verification/public-network-privacy-source.lean', 'public'],
                  'cwd': directory, 'lean_path': str(public_lib) if member == 'a' else directory+'/lib:'+base['lean_path'],
                  'stderr': directory+'/public-worker.stderr', 'compiler_sha256': sha(base['backend'][0]) if member == 'a' else None}
        source = ROOT/'Lean/scripts/verification/public-network-privacy-source.lean'
        if member == 'a':
            Path(directory+'/scripts/verification').mkdir(parents=True, exist_ok=True)
            Path(directory+'/scripts/verification/public-network-privacy-source.lean').write_bytes(source.read_bytes())
        elif 'wire-'+member not in progress['stages']:
            code = f'''import base64,hashlib,json
from pathlib import Path
p=Path({directory!r});(p/'scripts/verification').mkdir(parents=True,exist_ok=True)
(p/'scripts/verification/public-network-privacy-source.lean').write_bytes(base64.b64decode({base64.b64encode(source.read_bytes()).decode()!r}))
for n,v in {extra!r}.items():
 f=p/'lib'/n;f.parent.mkdir(parents=True,exist_ok=True);b=base64.b64decode(v)
 assert hashlib.sha256(b).hexdigest()=={extra_hash!r}[n]
 if f.exists():assert f.read_bytes()==b
 else:f.write_bytes(b)
print(hashlib.sha256(Path({base['backend'][0]!r}).read_bytes()).hexdigest())
'''
            compiler = execute(member, code, before, 180).strip()
            save(home/'spark-wire.json', {'compiler_sha256': compiler, 'modules': extra_hash, 'source': sha(source)})
            paid('wire-'+member)
        if member != 'a':
            worker['compiler_sha256'] = load(home/'spark-wire.json')['compiler_sha256']
        cfg['online_privacy'] = {'worker': worker, 'source_inputs': {directory+'/scripts/verification/public-network-privacy-source.lean': sha(source)},
                                 'journal': directory+'/boundary.jsonl', 'prefix': prefix}
        service_configs[owner] = cfg
    save(home/'prepared-services.json', service_configs)
    wire_closure(box, {**manifest, 'spark': {**manifest['spark'], 'service': service_configs['spark']}})
    if 'writer-barrier' not in progress['stages']:
        frozen = {}
        try:
            for owner in ('spark', 'mac'):
                frozen[owner] = freeze_writer(box, before, owner)
                save(home/'writer-barrier.json', frozen)
            states = Quorum(before['mac']['service']).collect('status')
            assert set(states) == set('abcd') and all(not v['intents'] and v['head']['seq'] == 27 for v in states.values())
            save(home/'barrier-status.json', states)
            paid('writer-barrier')
        except BaseException:
            for owner, record in frozen.items():
                spare.writer_signal(box, before, owner, 'SIGCONT', record)
            raise
    frozen = load(home/'writer-barrier.json')
    # Config and anchor stages are idempotent and retain every original DB/key.
    for member in 'bcd':
        if 'anchor-'+member in progress['stages']:
            continue
        item = manifest['nodes'][member]
        execute(member, 'import json\nfrom pathlib import Path\nPath('+repr(item['home']+'/config.json')+').write_text(json.dumps('+repr(configs[member])+')+"\\n")', manifest)
        restart_anchor(member, manifest)
        end = time.monotonic()+200
        client = Quorum(before['mac']['service']).nodes[member]
        while time.monotonic() < end:
            try:
                state = client.call('semantic-status')
                if state['prefix'] == {'seq': 27, 'head': literal[-1][2]} and state['backend'] and not state['warm_error']:
                    break
            except (ValueError, OSError, EOFError):
                pass
            time.sleep(1)
        else:
            raise TimeoutError('PUBLIC_TIMING_ANCHOR_NOT_READY:'+member)
        paid('anchor-'+member)
    save(box/'local-anchor/config.json', configs['a'])
    for owner in ('mac', 'spark'):
        manifest[owner]['service'] = service_configs[owner]
        manifest[owner]['controller'].update(public_timing='original-fixed-source/v1', release=revision)
    manifest['mac']['controller']['members']['a'] = [sys.executable, str(NETWORK/'live_timing.py'), 'anchor', str(box/'local-anchor/config.json')]
    for owner in ('spark', 'mac'):
        if 'candidate-'+owner in progress['stages']:
            continue
        retire_writer(box, before, owner, frozen[owner])
        if owner == 'spark':
            item = manifest['nodes']['c']
            command = [item['python'], item['code']+'/live_timing.py', 'coordinator', item['home']+'/ha/controller.json']
            code = f'''import json
from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'runtime/STOP').unlink(missing_ok=True)
(p/'service.json').write_text(json.dumps({manifest[owner]['service']!r})+'\\n')
(p/'controller.json').write_text(json.dumps({manifest[owner]['controller']!r})+'\\n')
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
'''
            execute('c', code, manifest)
            spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n', 90, allow_probe=False)
        else:
            module('timing_stop', 'public-recovery-isolation.py').stop(box)
            save(box/'ha/mac/service.json', manifest[owner]['service'])
            save(box/'ha/mac/controller.json', manifest[owner]['controller'])
            (box/'runtime/STOP').unlink(missing_ok=True)
            subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                            sys.executable, '-u', str(NETWORK/'live_timing.py'), 'coordinator', str(box/'ha/mac/controller.json')],
                           check=True, capture_output=True)
        paid('candidate-'+owner)
    manifest.update(protocol=protocol, release=revision,
                    public_timing={'release': revision, 'representative': 'original-fixed-source/v1', 'evidence': str(home)})
    save(manifest_path, manifest)
    assert [list(r) for r in spare.rows(service_configs['mac']['database'])] == literal
    save(home/'installed.json', {'release': revision, 'events': 27, 'head': literal[-1][2], 'protocol': protocol,
                                'before': sha(home/'before.json'), 'stages': progress['stages']})
    print('ORIGINAL LIVE PUBLIC TIMING ROUTING INSTALLED: original27 unchanged; actual epoch audit required', flush=True)


def restart_anchor(member, manifest):
    item = manifest['nodes'][member]
    command = [item['python'], item['code']+'/live_timing.py', 'host', item['home']]
    if member == 'd':
        execute(member, f'''import os,plistlib,subprocess
from pathlib import Path
p=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist';d='gui/'+str(os.getuid())
subprocess.run(['launchctl','bootout',d,str(p)],check=True)
v=plistlib.loads(p.read_bytes());v['ProgramArguments']={command!r};p.write_bytes(plistlib.dumps(v))
subprocess.run(['launchctl','bootstrap',d,str(p)],check=True)
''', manifest, 60)
    else:
        execute(member, f'''from pathlib import Path
p=Path({item['home']+'/unit.service'!r});p.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in p.read_text().splitlines())+'\\n')
''', manifest)
        prefix = 'sudo -n ' if member == 'c' else ''
        scope = '' if member == 'c' else '--user '
        target = '/etc/systemd/system' if member == 'c' else '~/.config/systemd/user'
        spare.transport.node(member).wsl(f'{prefix}systemctl {scope}stop homework-public-anchor-recovery.service\n{prefix}cp {shlex.quote(item["home"]+"/unit.service")} {target}/homework-public-anchor-recovery.service\n{prefix}systemctl {scope}daemon-reload\n{prefix}systemctl {scope}start homework-public-anchor-recovery.service\n', 150, allow_probe=False)


def restore_candidates(box, before):
    """Restore the paid original execution path if a new candidate cannot start."""
    home = box/'ha/live-timing'
    retired = {}
    for owner in ('spark', 'mac'):
        member = 'a' if owner == 'mac' else 'c'
        state = str(box/'runtime') if member == 'a' else before['nodes'][member]['home']+'/ha/runtime'
        codepath = str(NETWORK) if member == 'a' else before['nodes'][member]['code']
        code = f'''import json,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from anchor import public_key
from crypto import verify
v=verify(public_key({before['owners'][owner]!r}),'ha-coordinator',json.loads(Path({state+'/ha-status.json'!r}).read_text()))
print(json.dumps(v['boot']==boot_identity() and birth(v['pid'])==v['birth']))
'''
        if json.loads(execute(member, code, before, 40)):
            record = freeze_writer(box, before, owner)
        else:
            record = load(home/'writer-barrier.json')[owner]
        retire_writer(box, before, owner, record)
        retired[owner] = record
    module('timing_fallback_stop', 'public-recovery-isolation.py').stop(box)
    for owner in ('mac', 'spark'):
        if owner == 'mac':
            save(box/'ha/mac/service.json', before[owner]['service'])
            save(box/'ha/mac/controller.json', before[owner]['controller'])
        else:
            item = before['nodes']['c']
            command = [item['python'], item['code']+'/ha_coordinator.py', item['home']+'/ha/controller.json']
            execute('c', f'''import json
from pathlib import Path
p=Path({item['home']+'/ha'!r})
(p/'service.json').write_text(json.dumps({before[owner]['service']!r})+'\\n')
(p/'controller.json').write_text(json.dumps({before[owner]['controller']!r})+'\\n')
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
(p/'runtime/STOP').unlink(missing_ok=True)
''', before)
            spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n', 90, allow_probe=False)
    (box/'runtime/STOP').unlink(missing_ok=True)
    subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                    sys.executable, '-u', str(NETWORK/'ha_coordinator.py'), str(box/'ha/mac/controller.json')], check=True, capture_output=True)
    save(home/'candidate-fallback.json', {'retired': retired, 'at': time.time(),
        'source': before['source'], 'head': spare.rows(before['mac']['service']['database'])[-1][2]})
    progress = load(home/'progress.json')
    progress['stages'] = [s for s in progress['stages'] if not s.startswith('candidate-')]
    save(home/'progress.json', progress)
    if (home/'installed.json').exists():
        (home/'installed.json').rename(home/('routing-before-fallback-'+sha(home/'installed.json')[:12]+'.json'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    args = parser.parse_args()
    box = args.box.resolve()
    (box/'ha/live-timing').mkdir(exist_ok=True)
    lock = (box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    try:
        install(box)
    except BaseException as error:
        home = box/'ha/live-timing'
        recovered = {}
        if (home/'writer-barrier.json').exists():
            before = load(home/'before.json')
            for owner, record in load(home/'writer-barrier.json').items():
                try:
                    spare.writer_signal(box, before, owner, 'SIGCONT', record)
                    recovered[owner] = 'original coordinator/service resumed through original lease fencing'
                except Exception as problem:
                    # Never signal a recycled PID or resume a retired writer.
                    recovered[owner] = type(problem).__name__+': '+str(problem)
            if any(v != 'original coordinator/service resumed through original lease fencing' for v in recovered.values()):
                try:
                    restore_candidates(box, before)
                    recovered['fallback'] = 'original candidate configurations/entrypoints restored; original intent/ledger retained'
                except Exception as fallback_error:
                    recovered['fallback'] = type(fallback_error).__name__+': '+str(fallback_error)
        save(home/'recovery-required.json', {'error': str(error), 'original_writer_recovery': recovered,
                                           'progress': load(home/'progress.json') if (home/'progress.json').exists() else None})
        raise
