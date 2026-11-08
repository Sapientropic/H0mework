"""Install explicit, pre-enrolled Mac/Spark failover on the original journals."""
import argparse
import base64
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]; NETWORK = ROOT/'Verification/public-audit/network'
sys.path[:0] = [str(NETWORK), str(ROOT/'ComputeNode/mac')]
from crypto import app_private, digest, sign, verify
from recovery_loop import save
from anchor import public_key
from pcnode import Config, Node


def node(member):
    tag, filename = {'b': ('pc','pcnode.json'), 'c': ('spark','sparknode.local.json'), 'd': ('studio','studionode.local.json')}[member]
    return Node(Config.load(ROOT/'ComputeNode'/filename), ROOT/'ComputeNode/state'/('public-anchor-'+tag+'-20261102'))


def remote(member, code, timeout=40, python='python3'):
    return node(member).wsl(shlex.quote(python)+" - <<'HA'\n"+code+"\nHA\n", timeout, allow_probe=False)


KEY_CODE = """from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding,PrivateFormat,NoEncryption
p=Path(LOCATION);p.mkdir(mode=0o700,parents=True,exist_ok=True);key=p/'app.key'
if not key.exists():key.write_bytes(Ed25519PrivateKey.generate().private_bytes(Encoding.PEM,PrivateFormat.PKCS8,NoEncryption()));key.chmod(0o600)
from cryptography.hazmat.primitives.serialization import load_pem_private_key
print(load_pem_private_key(key.read_bytes(),None).public_key().public_bytes_raw().hex())
"""


def deploy(box):
    ha = box/'ha'; ha.mkdir(exist_ok=True, mode=0o700)
    original = json.loads((box/'service.json').read_text()); old_loop = json.loads((box/'loop.json').read_text())
    previous = json.loads((box/'deployment.json').read_text()); addresses = json.loads((ha/'addresses.json').read_text())
    path = ha/'deployment.json'; record = json.loads(path.read_text()) if path.exists() else {'stages': [], 'physical_host_reboots': 0}
    def paid(stage):
        record['stages'].append(stage); save(path, record); print('HA INSTALLED '+stage, flush=True)
    mac_owner = ha/'mac/owner'; mac_owner.parent.mkdir(exist_ok=True)
    spark_home = previous['nodes']['c']['home']; spark_ha = spark_home+'/ha'
    if 'owners' not in record:
        code = KEY_CODE.replace('LOCATION', repr(str(mac_owner)))
        mac_pub = subprocess.check_output([sys.executable, '-c', code], text=True).strip()
        spark_pub = remote('c', KEY_CODE.replace('LOCATION', repr(spark_ha+'/owner'))).decode().strip()
        record['owners'] = {'mac': {'app': mac_pub}, 'spark': {'app': spark_pub}}
        record['source'] = original['source']; record['trust'] = original['anchors']['trust']
        paid('owners')
    names = ['anchor.py','crypto.py','quorum.py','challenge_anchor.py','service.py','verify.py','recovery_loop.py',
             'ha_anchor.py','ha_quorum.py','ha_service.py','ha_host.py','ha_coordinator.py']
    files = {name: (NETWORK/name).read_bytes() for name in names}
    inventory = {name: hashlib.sha256(raw).hexdigest() for name,raw in files.items()}
    revision = digest(inventory); record['protocol'] = inventory; record['release'] = revision
    settings = {'owners': record['owners'], 'trust': record['trust'], 'lease_seconds': 30}
    if 'baseline' not in record['stages']:
        db = sqlite3.connect(original['database']); target = sqlite3.connect(ha/'baseline-service.sqlite')
        db.backup(target); target.close(); literal = db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall(); db.close()
        if len(literal) != 7:raise ValueError('HA_ORIGINAL_SEVEN_EVENT_BASELINE_REQUIRED')
        save(ha/'baseline.json', {'rows': literal, 'service': original, 'loop': old_loop,
                                 'previous_final': json.loads((box/'final-check.json').read_text())})
        spec = importlib.util.spec_from_file_location('owned_original_stop', Path(__file__).with_name('public-recovery-isolation.py'))
        old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old); old.stop(box)
        paid('baseline')
    for member in 'bcd':
        stage = 'anchor-'+member
        if stage in record['stages']:continue
        item = previous['nodes'][member]; release = item['home']+'/code/'+revision
        payload = {name: base64.b64encode(raw).decode() for name,raw in files.items()}
        code = f"import base64,hashlib,json\nfrom pathlib import Path\np=Path({release!r});p.mkdir(parents=True,exist_ok=True)\nfiles={payload!r}\nfor name,raw in files.items():(p/name).write_bytes(base64.b64decode(raw))\nassert {{n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in files}}=={inventory!r}\n"
        remote(member, code)
        n = node(member); unit = 'homework-public-anchor-recovery.service'
        if member == 'd':
            remote(member, "import os,subprocess\nfrom pathlib import Path\np=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist';d='gui/'+str(os.getuid())\nif subprocess.run(['launchctl','print',d+'/com.homework.public-anchor-recovery'],capture_output=True).returncode==0:subprocess.run(['launchctl','bootout',d,str(p)],check=True)")
        else:
            n.wsl(('sudo -n ' if member == 'c' else '')+'systemctl '+('--user ' if member == 'b' else '')+'stop '+unit+'\n',30,allow_probe=False)
        code = f"import json,os,plistlib,subprocess,sys\nfrom pathlib import Path\nsys.path.insert(0,{release!r})\nfrom recovery_loop import birth,save\nh=Path({item['home']!r});p=h/'config.json';cfg=json.loads(p.read_text());cfg['ha']={settings!r};save(p,cfg)\nr=h/'state/anchor-process.json'\nif r.exists():\n v=json.loads(r.read_text());assert birth(v['pid'])!=v['birth'],'original anchor still alive';r.unlink()\n"
        command = [item['python'], release+'/ha_host.py', item['home']]
        if member == 'd':
            code += f"p=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist';u=plistlib.loads(p.read_bytes());u['ProgramArguments']={command!r};p.write_bytes(plistlib.dumps(u))\nsubprocess.run(['launchctl','bootstrap','gui/'+str(os.getuid()),str(p)],check=True)\n"
        else:
            code += f"p=h/'unit.service';u=p.read_text();u='\\n'.join('ExecStart='+{shlex.join(command)!r} if line.startswith('ExecStart=') else line for line in u.splitlines())+'\\n';p.write_text(u)\n"
        remote(member, code, python=item['python'])
        if member == 'c':
            n.wsl(f'sudo -n install -m 644 {shlex.quote(item["home"]+"/unit.service")} /etc/systemd/system/{unit}\nsudo -n systemctl daemon-reload\nsudo -n systemctl start {unit}\n',30,allow_probe=False)
        elif member == 'b':
            n.wsl(f'cp {shlex.quote(item["home"]+"/unit.service")} ~/.config/systemd/user/{unit}\nsystemctl --user daemon-reload\nsystemctl --user start {unit}\n',30,allow_probe=False)
        record.setdefault('nodes', {})[member] = {**item, 'code': release, 'protocol': inventory}
        paid(stage)
    if 'local-anchor' not in record['stages']:
        anchor_path = box/'local-anchor/config.json'; cfg = json.loads(anchor_path.read_text())
        save(ha/'original-local-anchor-config.json', cfg); save(anchor_path, {**cfg, 'ha': settings})
        paid('local-anchor')
    if 'spark-service' not in record['stages']:
        # Only this service identity and its RPC client credentials are copied.
        # Each anchor's signing private key remains on its original machine.
        credentials = {}
        for rel in ('ca.pem','server/cert.pem','server/tls.key','server/app.key'):
            credentials['service-pki/'+rel] = base64.b64encode((Path(original['pki'])/rel).read_bytes()).decode()
        for member, endpoint in original['anchors']['endpoints'].items():
            for rel in ('ca.pem','server/cert.pem','server/tls.key','server/app.key'):
                credentials['rpc-'+member+'/'+rel] = base64.b64encode((Path(endpoint['pki'])/rel).read_bytes()).decode()
        endpoints = {member: {**endpoint, 'host': addresses[member],
                     'port': 43192 if member == 'a' else 43191, 'pki': spark_ha+'/rpc-'+member}
                     for member,endpoint in original['anchors']['endpoints'].items()}
        cfg = {**original, 'pki': spark_ha+'/service-pki', 'anchors': {'trust': record['trust'], 'endpoints': endpoints},
               'database': spark_ha+'/standby/service.sqlite', 'backend_error': spark_ha+'/standby/source.log',
               'lean': spark_ha+'/lean', 'lean_path': spark_ha+'/lean/lib', 'bind': '0.0.0.0',
               'backend': ['runtime/retained/lean', '--trust=0', '-j1',
                           '--run', spark_ha+'/lean/public-scoped-audit-source.lean', 'private-one'],
               'ha': {'owner': 'spark', 'owner_profile': spark_ha+'/owner'}}
        controller = {'state': spark_ha+'/runtime', 'service': spark_ha+'/service.json', 'interval': 2}
        code = f"import base64,json,sys\nfrom pathlib import Path\nsys.path.insert(0,{record['nodes']['c']['code']!r})\nfrom recovery_loop import save\np=Path({spark_ha!r});(p/'standby').mkdir(mode=0o700,exist_ok=True)\nfor name,raw in {credentials!r}.items():\n f=p/name;f.parent.mkdir(mode=0o700,parents=True,exist_ok=True);f.write_bytes(base64.b64decode(raw));f.chmod(0o600)\nsave(p/'service.json',{cfg!r});save(p/'controller.json',{controller!r})\n"
        remote('c', code)
        record['spark'] = {'service': cfg, 'controller': controller}; paid('spark-service')
    if 'mac-service' not in record['stages']:
        cfg = {**original, 'bind': '0.0.0.0', 'test_boundary': 'after-source',
               'ha': {'owner': 'mac', 'owner_profile': str(mac_owner)}}
        save(ha/'mac/service.json', cfg)
        commands = {member: value['command'] for member,value in old_loop['members'].items()}
        commands['a'] = [sys.executable, str(NETWORK/'ha_anchor.py'), str(box/'local-anchor/config.json')]
        controller = {'state': old_loop['state'], 'service': str(ha/'mac/service.json'), 'members': commands, 'interval': 2}
        save(ha/'mac/controller.json', controller); record['mac'] = {'service': cfg, 'controller': controller}; paid('mac-service')
    if 'mac-running' not in record['stages']:
        subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                        sys.executable, '-u', str(NETWORK/'ha_coordinator.py'), str(ha/'mac/controller.json')], cwd=ROOT,check=True,capture_output=True)
        end = time.monotonic()+120
        while time.monotonic()<end:
            p=box/'runtime/ha-status.json'
            if p.exists():
                value=verify(public_key(record['owners']['mac']),'ha-coordinator',json.loads(p.read_text()))
                if value['phase']=='leader' and value['head']['seq']==7:break
            time.sleep(.5)
        else:raise TimeoutError('Mac HA leader did not recover original prefix')
        paid('mac-running')
    if 'spark-running' not in record['stages']:
        release = record['nodes']['c']['code']; cfg = record['spark']['controller']
        command = ['/usr/bin/python3', release+'/ha_coordinator.py', spark_ha+'/controller.json']
        unit = '[Unit]\nDescription=Public source HA standby\nAfter=network-online.target\n[Service]\nUser=jtwm\nExecStart='+shlex.join(command)+'\nRestart=on-failure\nRestartSec=3\nCPUQuota=50%\nMemoryMax=2G\nTimeoutStopSec=20\n[Install]\nWantedBy=multi-user.target\n'
        remote('c',f"from pathlib import Path\nPath({spark_ha+'/ha.service'!r}).write_text({unit!r})")
        node('c').wsl(f'sudo -n install -m 644 {shlex.quote(spark_ha+"/ha.service")} /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl enable --now homework-public-source-ha.service\n',30,allow_probe=False)
        paid('spark-running')
    print('HA DEPLOYMENT READY: same source and original four journals; two pre-enrolled physical candidates', flush=True)


def refresh(box):
    """Roll only this workload's processes; preserve every paid event and key."""
    ha = box/'ha'; path = ha/'deployment.json'; record = json.loads(path.read_text())
    original = json.loads((box/'service.json').read_text())
    with sqlite3.connect(Path(original['database']).as_uri()+'?mode=ro', uri=True) as db:
        expected_seq = db.execute('SELECT count(*) FROM events').fetchone()[0]
    frozen = ha/'actual-01/deployment.json'
    if not frozen.exists():
        save(frozen, record)
    names = list(record['protocol']); files = {name: (NETWORK/name).read_bytes() for name in names}
    inventory = {name: hashlib.sha256(raw).hexdigest() for name,raw in files.items()}
    revision = digest(inventory); progress = ha/'refresh.json'
    record['mac']['controller']['release']=revision
    save(ha/'mac/controller.json',record['mac']['controller'])
    record['spark']['controller']['release']=revision
    receipt = json.loads(progress.read_text()) if progress.exists() else {'release': revision, 'stages': []}
    if receipt['release'] != revision:
        if set(receipt['stages']) != {'upload-b','upload-c','upload-d','spark','mac','anchor-b','anchor-c','anchor-d'}:
            raise ValueError('unfinished refresh belongs to a different release')
        progress.rename(progress.with_name('refresh-'+receipt['release']+'.json'))
        receipt = {'release': revision, 'stages': []}
    def paid(stage):
        receipt['stages'].append(stage); save(progress, receipt); save(path, record)
        print('HA REFRESH '+stage, flush=True)
    for member in 'bcd':
        if 'upload-'+member in receipt['stages']:continue
        item = record['nodes'][member]; release = item['home']+'/code/'+revision
        payload = {name: base64.b64encode(raw).decode() for name,raw in files.items()}
        remote(member, f"import base64,hashlib\nfrom pathlib import Path\np=Path({release!r});p.mkdir(parents=True,exist_ok=True)\nfor n,r in {payload!r}.items():(p/n).write_bytes(base64.b64decode(r))\nassert {{n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in {names!r}}}=={inventory!r}")
        record['nodes'][member] = {**item, 'code': release, 'protocol': inventory}; paid('upload-'+member)
    if 'spark' not in receipt['stages']:
        item = record['nodes']['c']; home = item['home']; release = item['code']
        code = f"from pathlib import Path\nimport subprocess,json\nPath({home+'/ha/controller.json'!r}).write_text(json.dumps({record['spark']['controller']!r})+'\\n')\np=Path({home+'/ha/ha.service'!r});u=p.read_text();u='\\n'.join('ExecStart='+{shlex.join(['/usr/bin/python3',release+'/ha_coordinator.py',home+'/ha/controller.json'])!r} if l.startswith('ExecStart=') else l for l in u.splitlines())+'\\n';p.write_text(u)\n"
        remote('c', code)
        node('c').wsl(f'sudo -n systemctl stop homework-public-source-ha.service\nsudo -n install -m 644 {shlex.quote(home+"/ha/ha.service")} /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl start homework-public-source-ha.service\n', 40, allow_probe=False)
        paid('spark')
    for member in 'bcd':
        stage='anchor-'+member
        if stage in receipt['stages']:continue
        item=record['nodes'][member];home=item['home'];command=[item['python'],item['code']+'/ha_host.py',home]
        probe=f"import json,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom recovery_loop import birth\np=Path({home+'/status.json'!r})\nr=json.loads(p.read_text())['body']['process'] if p.exists() else {{}}\nprint(json.dumps(r.get('argv')=={[item['python'],item['code']+'/semantic_anchor.py' if record.get('semantic') and member in record['semantic']['native_members'] else item['code']+'/ha_anchor.py',home+'/config.json']!r} and birth(r.get('pid',-1))==r.get('birth')))"
        running=json.loads(remote(member,probe,python=item['python']))
        if not running:
            if member=='d':
                code=f"from pathlib import Path\nimport os,plistlib,subprocess\np=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist';domain='gui/'+str(os.getuid());subprocess.run(['launchctl','bootout',domain,str(p)],check=True);u=plistlib.loads(p.read_bytes());u['ProgramArguments']={command!r};p.write_bytes(plistlib.dumps(u));subprocess.run(['launchctl','bootstrap',domain,str(p)],check=True)\n"
                remote(member,code,python=item['python'])
            else:
                remote(member,f"from pathlib import Path\np=Path({home+'/unit.service'!r});p.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in p.read_text().splitlines())+'\\n')")
                prefix='sudo -n ' if member=='c' else '';scope='' if member=='c' else '--user ';target='/etc/systemd/system' if member=='c' else '~/.config/systemd/user'
                node(member).wsl(f'{prefix}systemctl {scope}stop homework-public-anchor-recovery.service\n{prefix}cp {shlex.quote(home+"/unit.service")} {target}/homework-public-anchor-recovery.service\n{prefix}systemctl {scope}daemon-reload\n{prefix}systemctl {scope}start homework-public-anchor-recovery.service\n',40,allow_probe=False)
        # A rolling anchor restart must rejoin before touching the next one.
        from ha_quorum import Quorum
        client=Quorum(record['mac']['service']).nodes[member];end=time.monotonic()+90
        while time.monotonic()<end:
            try:
                if client.status()['head']['seq']>=expected_seq:break
            except (ValueError,OSError,EOFError):pass
            time.sleep(.3)
        else:raise TimeoutError('refreshed anchor did not return: '+member)
        paid(stage)
    if 'mac' not in receipt['stages']:
        from recovery_loop import birth
        state_path=box/'runtime/ha-status.json';running=False
        if state_path.exists():
            value=verify(public_key(record['owners']['mac']),'ha-coordinator',json.loads(state_path.read_text()))
            running=(value['configuration']==digest(record['mac']['controller']) and
                     time.time()-value['at']<5 and birth(value['pid'])==value['birth'])
        if not running:
            module_stop = importlib.util.spec_from_file_location('stop_owned_ha', Path(__file__).with_name('public-recovery-isolation.py'))
            stop = importlib.util.module_from_spec(module_stop); module_stop.loader.exec_module(stop); stop.stop(box)
            subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                            sys.executable,'-u',str(NETWORK/'ha_coordinator.py'),str(ha/'mac/controller.json')], cwd=ROOT, check=True,capture_output=True)
        end=time.monotonic()+60
        while time.monotonic()<end:
            value=verify(public_key(record['owners']['mac']),'ha-coordinator',json.loads((box/'runtime/ha-status.json').read_text()))
            if value['phase'] in {'leader','standby'} and (value.get('head') or {}).get('seq',-1)>=expected_seq and time.time()-value['at']<5 and birth(value['pid'])==value['birth']:break
            time.sleep(.2)
        else:raise TimeoutError('refreshed Mac candidate did not return')
        paid('mac')
    record['protocol']=inventory;record['release']=revision;save(path,record)
    print('HA ROLLING REFRESH COMPLETE: '+str(expected_seq)+' original events and original keys retained',flush=True)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path)
    parser.add_argument('--refresh',action='store_true');args=parser.parse_args()
    (refresh if args.refresh else deploy)(args.box.resolve())
