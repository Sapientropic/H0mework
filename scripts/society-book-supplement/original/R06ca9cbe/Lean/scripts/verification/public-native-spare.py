"""Admit the pre-enrolled fourth native verifier on the original committed prefix."""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key
from crypto import digest, verify
from ha_quorum import Quorum
from recovery_loop import save

spec = importlib.util.spec_from_file_location('spare_transport', Path(__file__).with_name('public-ha-deploy.py'))
transport = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transport)


def load(path):
    return json.loads(Path(path).read_text())


def rows(path):
    with sqlite3.connect(Path(path).as_uri()+'?mode=ro', uri=True) as db:
        return db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()


def execute(member, code, manifest, timeout=180):
    if member == 'a':
        return subprocess.check_output([sys.executable, '-c', code], text=True, timeout=timeout)
    item = manifest['nodes'][member]
    return transport.remote(member, code, timeout=timeout, python=item['python']).decode()


def readiness(box):
    home = box/'ha/native-spare'
    path = home/'admission.json'
    manifest = load(box/'ha/deployment.json')
    literal = rows(manifest['mac']['service']['database'])
    assert len(literal) == 27
    if path.exists():
        assert load(path)['point']['prefix'] == {'seq': 27, 'head': literal[-1][2]}
        return
    ready = load(home/'ready-studio.json')
    assert ready['original_prefix'] == {'seq': 27, 'head': literal[-1][2]}
    point = {'source': manifest['source'], 'stream': 'recovery', 'cluster': digest(manifest['trust']),
             'prefix': ready['original_prefix'], 'previous': list('abc'), 'current': list('abcd'),
             'descriptors': {'base': manifest['semantic']['descriptor'],
                 **{name: manifest[name]['descriptor'] for name in ('governance', 'energy', 'continuation', 'handoff')}}}
    def inspect(member):
        if member == 'a':
            cfgpath = str(box/'local-anchor/config.json')
            codepath = str(NETWORK)
        else:
            item = manifest['nodes'][member]
            cfgpath, codepath = item['home']+'/config.json', item['code']
        source = ready['base_semantic'] if member == 'd' else manifest['semantic']['configurations'][member]
        code = f'''import hashlib,json,sqlite3,sys,time
from pathlib import Path
sys.path.insert(0,{codepath!r})
from source_semantics import Engine
from crypto import app_private,sign
import governance,energy
c=json.loads(Path({cfgpath!r}).read_text());s={source!r};point={point!r}
with sqlite3.connect(Path(c['database']).as_uri()+'?mode=ro',uri=True) as db:
 r=db.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq',('recovery',)).fetchall()
assert len(r)==27 and r[-1][2]==point['prefix']['head']
e=Engine({{**s,'replay_seconds':300}})
try:
 e.sync(r,deadline=time.monotonic()+300);status=e.status();assert status['prefix']==point['prefix'] and status['backend']
 value={{'point':point,'member':{member!r},'compiler':s['descriptor']['compiler'],'backend':status['backend'],
        'source_config_sha256':hashlib.sha256(json.dumps(s,sort_keys=True).encode()).hexdigest(),'at':time.time()}}
 print(json.dumps(sign(app_private(Path(c['pki'])/'anchor'),'native-source-ready',value)))
finally:e.close();governance.close_readers();energy.close_readers()
'''
        value = json.loads(execute(member, code, manifest, 360))
        actual = verify(public_key(manifest['trust']['members'][member]), 'native-source-ready', value)
        assert actual['point'] == point and actual['member'] == member
        save(home/('ready-'+member+'.json'), value)
        print('ACTUAL NATIVE READY '+member+': original27; same source/compiler; own anchor signature', flush=True)
        return {'member': member, 'receipt': value}
    with ThreadPoolExecutor(max_workers=4) as pool:
        votes = list(pool.map(inspect, 'abcd'))
    save(path, {'point': point, 'votes': votes})


def restart(member, manifest):
    item = manifest['nodes'][member]
    command = [item['python'], item['code']+'/native_spare.py', 'host', item['home']]
    if member == 'd':
        code = f'''import os,plistlib,subprocess
from pathlib import Path
p=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist';d='gui/'+str(os.getuid())
subprocess.run(['launchctl','bootout',d,str(p)],check=True)
v=plistlib.loads(p.read_bytes());v['ProgramArguments']={command!r};p.write_bytes(plistlib.dumps(v))
subprocess.run(['launchctl','bootstrap',d,str(p)],check=True)
'''
        execute(member, code, manifest, 40)
    else:
        code = f"from pathlib import Path\np=Path({item['home']+'/unit.service'!r});p.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in p.read_text().splitlines())+'\\n')\n"
        execute(member, code, manifest, 40)
        prefix = 'sudo -n ' if member == 'c' else ''
        scope = '' if member == 'c' else '--user '
        target = '/etc/systemd/system' if member == 'c' else '~/.config/systemd/user'
        transport.node(member).wsl(f'{prefix}systemctl {scope}stop homework-public-anchor-recovery.service\n{prefix}cp {shlex.quote(item["home"]+"/unit.service")} {target}/homework-public-anchor-recovery.service\n{prefix}systemctl {scope}daemon-reload\n{prefix}systemctl {scope}start homework-public-anchor-recovery.service\n', 150, allow_probe=False)


def writer_signal(box, manifest, owner, action, record=None):
    member = 'a' if owner == 'mac' else 'c'
    state = str(box/'runtime/ha-status.json') if owner == 'mac' else manifest['nodes']['c']['home']+'/ha/runtime/ha-status.json'
    codepath = str(NETWORK) if owner == 'mac' else manifest['nodes']['c']['code']
    code = f'''import json,os,signal,sys,time
from pathlib import Path
sys.path.insert(0,{codepath!r})
from anchor import public_key
from crypto import verify
from recovery_loop import birth,boot_identity
v={record!r}
if v is None:
 v=verify(public_key({manifest['owners'][owner]!r}),'ha-coordinator',json.loads(Path({state!r}).read_text()))
 assert v['owner']=={owner!r} and v['source']=={manifest['source']!r} and time.time()-v['at']<15
assert v['boot']==boot_identity() and birth(v['pid'])==v['birth']
os.kill(v['pid'],signal.{action})
r=v.get('service')
if r:
 assert birth(r['pid'])==r['birth'] and os.getpgid(r['pid'])==r['pgid']==r['pid']
 os.killpg(r['pid'],signal.{action})
print(json.dumps(v))
'''
    return json.loads(execute(member, code, manifest, 40))


def retire_writer(box, manifest, owner, record):
    member = 'a' if owner == 'mac' else 'c'
    codepath = str(NETWORK) if owner == 'mac' else manifest['nodes']['c']['code']
    state = str(box/'runtime') if owner == 'mac' else manifest['nodes']['c']['home']+'/ha/runtime'
    script = f'''import os,signal,sys,time
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
v={record!r};p=Path({state!r});(p/'STOP').touch()
if v['boot']==boot_identity() and birth(v['pid'])==v['birth']:
 os.kill(v['pid'],signal.SIGCONT)
 end=time.monotonic()+60
 while birth(v['pid'])==v['birth'] and time.monotonic()<end:time.sleep(.1)
 assert birth(v['pid'])!=v['birth'],'frozen coordinator did not retire'
print('WRITER_RETIRED_WITHOUT_RESUMING_SERVICE')
'''
    execute(member, script, manifest, 75)


def install(box):
    home = box/'ha/native-spare'
    manifest = load(box/'ha/deployment.json')
    certificate = load(home/'admission.json')
    literal = rows(manifest['mac']['service']['database'])
    assert len(literal) == 27 and certificate['point']['prefix']['head'] == literal[-1][2]
    progress_path = home/'install-progress.json'
    progress = load(progress_path) if progress_path.exists() else {'stages': []}
    def paid(stage):
        if stage not in progress['stages']:
            progress['stages'].append(stage)
        save(progress_path, progress)
        save(box/'ha/deployment.json', manifest)
        print('NATIVE ADMISSION INSTALLED '+stage, flush=True)
    required = {'writer-barrier', 'config-b', 'config-c', 'config-d', 'anchor-d', 'anchor-b',
                'anchor-c', 'local-config', 'services', 'source-command'}
    if required <= set(progress['stages']) and (home/'installed.json').is_file():
        assert manifest.get('native_admission') == certificate
        installed = load(home/'installed.json')
        assert installed['admission'] == digest(certificate) and installed['release'] == manifest['release']
        assert installed['original_events'] == 27 and installed['head'] == literal[-1][2]
        assert manifest['protocol'] == {name: hashlib.sha256((NETWORK/name).read_bytes()).hexdigest()
                                        for name in manifest['protocol']}
        print('NATIVE ADMISSION ALREADY INSTALLED: retain the paid rollout; use the independent consumer', flush=True)
        return
    ready = load(home/'ready-studio.json')
    mutation_stages = {'config-b', 'config-c', 'config-d', 'anchor-d', 'anchor-b', 'anchor-c', 'local-config'}
    if 'writer-barrier' not in progress['stages'] or not mutation_stages <= set(progress['stages']):
        frozen = {}
        prior_frozen = load(home/'writer-barrier.json') if (home/'writer-barrier.json').exists() else {}
        try:
            for owner in ('spark', 'mac'):
                try:
                    frozen[owner] = writer_signal(box, manifest, owner, 'SIGSTOP', prior_frozen.get(owner))
                except (RuntimeError, subprocess.CalledProcessError):
                    frozen[owner] = writer_signal(box, manifest, owner, 'SIGSTOP')
                save(home/'writer-barrier.json', frozen)
            states = Quorum(manifest['mac']['service']).collect('status')
            assert set(states) == set('abcd')
            assert all({k: v['head'][k] for k in ('seq', 'head')} == certificate['point']['prefix']
                       and not v['intents'] for v in states.values())
            assert rows(manifest['mac']['service']['database']) == literal
            save(home/'writer-barrier-status.json', states)
            paid('writer-barrier')
        except BaseException:
            for owner, record in frozen.items():
                writer_signal(box, manifest, owner, 'SIGCONT', record)
            raise
    protocol = {name: hashlib.sha256((NETWORK/name).read_bytes()).hexdigest()
                for name in [*manifest['protocol'], 'native_spare.py']}
    revision = digest(protocol)
    for member in 'bcd':
        stage = 'config-'+member
        if stage in progress['stages']:
            continue
        item = manifest['nodes'][member]
        original = json.loads(execute(member, f"from pathlib import Path\nprint(Path({item['home']+'/config.json'!r}).read_text())\n", manifest))
        save(home/('original-'+member+'-config.json'), original)
        cfg = copy.deepcopy(original)
        cfg.update(governance_members=list('abcd'), native_admission=certificate)
        if member == 'd':
            cfg.update({name: ready['configurations'][name] for name in ('governance', 'energy', 'continuation', 'handoff')})
            cfg['semantic'] = ready['base_semantic']
        cfg['semantic'] = copy.deepcopy(cfg['semantic'])
        cfg['semantic'].update(background_warmup=True, warm_on_start=True)
        context = {name: cfg[name] for name in ('registry', 'ha', 'semantic_policy', 'governance', 'energy', 'continuation', 'handoff')}
        context.update(source=manifest['source'], stream='recovery')
        cfg['semantic']['governance_context'] = context
        release = item['home']+'/code/'+revision
        payload = {name: base64.b64encode((NETWORK/name).read_bytes()).decode() for name in protocol}
        code = f'''import base64,hashlib,json,sys
from pathlib import Path
p=Path({release!r});p.mkdir(parents=True,exist_ok=True)
for n,r in {payload!r}.items():
 b=base64.b64decode(r);assert hashlib.sha256(b).hexdigest()=={protocol!r}[n];(p/n).write_bytes(b)
sys.path.insert(0,str(p))
from native_spare import admission
admission({cfg!r})
from recovery_loop import save
save(Path({item['home']+'/config.json'!r}),{cfg!r})
'''
        execute(member, code, manifest)
        manifest['nodes'][member] = {**item, 'code': release, 'protocol': protocol}
        manifest['semantic']['configurations'][member] = cfg['semantic']
        for name in ('governance', 'energy', 'continuation', 'handoff'):
            manifest[name]['configurations'][member] = cfg[name]
        paid(stage)
    # Restart one owned anchor at a time; retain every pending intent and lease.
    for member in 'dbc':
        stage = 'anchor-'+member
        if stage in progress['stages']:
            continue
        item = manifest['nodes'][member]
        probe = f'''import json,sys
from pathlib import Path
sys.path.insert(0,{item['code']!r})
from recovery_loop import birth
p=Path({item['home']+'/status.json'!r});v=json.loads(p.read_text())['body'] if p.exists() else {{}}
r=v.get('process',{{}})
print(json.dumps(v.get('entrypoint')=='native_spare.py' and r.get('argv')=={[item['python'],item['code']+'/native_spare.py','anchor',item['home']+'/config.json']!r} and birth(r.get('pid',-1))==r.get('birth')))
'''
        if not json.loads(execute(member, probe, manifest, 40)):
            restart(member, manifest)
        client = Quorum(manifest['mac']['service']).nodes[member]
        end = time.monotonic()+180
        while time.monotonic() < end:
            try:
                status = client.call('semantic-status')
                if status['prefix'] == certificate['point']['prefix'] and status['backend']:
                    break
            except (ValueError, OSError, EOFError):
                pass
            time.sleep(1)
        else:
            raise TimeoutError('NATIVE_ADMISSION_ANCHOR_NOT_READY:'+member)
        paid(stage)
    if 'local-config' not in progress['stages']:
        cfg = load(box/'local-anchor/config.json')
        save(home/'original-a-config.json', cfg)
        cfg.update(governance_members=list('abcd'), native_admission=certificate)
        save(box/'local-anchor/config.json', cfg)
        manifest['mac']['controller']['members']['a'] = [sys.executable, str(NETWORK/'native_spare.py'), 'anchor', str(box/'local-anchor/config.json')]
        manifest['semantic']['configurations']['a'] = cfg['semantic']
        paid('local-config')
    if 'services' not in progress['stages']:
        for owner in ('mac', 'spark'):
            manifest[owner]['service']['governance_members'] = list('abcd')
            manifest[owner]['controller']['release'] = revision
        save(box/'ha/mac/service.json', manifest['mac']['service'])
        save(box/'ha/mac/controller.json', manifest['mac']['controller'])
        item = manifest['nodes']['c']
        code = f"from pathlib import Path\nimport json\nPath({item['home']+'/ha/service.json'!r}).write_text(json.dumps({manifest['spark']['service']!r})+'\\n')\nPath({item['home']+'/ha/controller.json'!r}).write_text(json.dumps({manifest['spark']['controller']!r})+'\\n')\n"
        execute('c', code, manifest)
        frozen = load(home/'writer-barrier.json')
        retire_writer(box, manifest, 'spark', frozen['spark'])
        execute('c', f"from pathlib import Path\nPath({item['home']+'/ha/runtime/STOP'!r}).unlink(missing_ok=True)\n", manifest)
        transport.node('c').wsl('sudo -n systemctl restart homework-public-source-ha.service\n', 40, allow_probe=False)
        old_spec = importlib.util.spec_from_file_location('spare_stop', Path(__file__).with_name('public-recovery-isolation.py'))
        old = importlib.util.module_from_spec(old_spec)
        old_spec.loader.exec_module(old)
        retire_writer(box, manifest, 'mac', frozen['mac'])
        old.stop(box)
        (box/'runtime/STOP').unlink(missing_ok=True)
        subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                        sys.executable, '-u', str(NETWORK/'ha_coordinator.py'), str(box/'ha/mac/controller.json')],
                       check=True, capture_output=True)
        paid('services')
    if 'source-command' not in progress['stages']:
        item = manifest['nodes']['c']
        command = ['/usr/bin/python3', item['code']+'/ha_coordinator.py', item['home']+'/ha/controller.json']
        code = f"from pathlib import Path\np=Path({item['home']+'/ha/ha.service'!r});p.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in p.read_text().splitlines())+'\\n')\n"
        execute('c', code, manifest)
        transport.node('c').wsl(f'sudo -n install -m 644 {shlex.quote(item["home"]+"/ha/ha.service")} /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n', 150, allow_probe=False)
        paid('source-command')
    manifest.update(native_admission=certificate, protocol=protocol, release=revision)
    manifest['semantic']['native_members'] = 'abcd'
    save(box/'ha/deployment.json', manifest)
    assert rows(manifest['mac']['service']['database']) == literal
    save(home/'installed.json', {'stages': progress['stages'], 'admission': digest(certificate),
                               'release': revision, 'original_events': 27, 'head': literal[-1][2]})
    print('FOUR NATIVE ANCHORS ADMITTED: original27 and historical policies retained; native threshold3', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    parser.add_argument('phase', choices=('ready', 'install'))
    args = parser.parse_args()
    (readiness if args.phase == 'ready' else install)(args.box.resolve())
