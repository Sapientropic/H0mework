"""Exercise the continuous original service on four physical anchor machines."""
from concurrent.futures import ThreadPoolExecutor
import argparse
import base64
import importlib.util
import json
import os
from pathlib import Path
import signal
import sqlite3
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT / 'Verification/public-audit/network'
sys.path[:0] = [str(NETWORK), str(ROOT/'ComputeNode/mac')]
from pcnode import Config, Node
from crypto import digest, verify
from anchor import public_key
from client import exchange
from exercise import replay
from recovery_loop import birth, save

spec = importlib.util.spec_from_file_location('service_recovery_actual', Path(__file__).with_name('public-recovery-audit.py'))
local = importlib.util.module_from_spec(spec);spec.loader.exec_module(local)


def remote(member):
    tag, filename = {'b': ('pc','pcnode.json'), 'c': ('spark','sparknode.local.json'), 'd': ('studio','studionode.local.json')}[member]
    cfg = Config.load(ROOT/'ComputeNode'/filename)
    return Node(cfg, ROOT/'ComputeNode/state'/('public-anchor-'+tag+'-20261102'))


def python(node, code):
    return node.wsl("python3 - <<'ACTUAL'\n"+code+"\nACTUAL\n",30,allow_probe=False)


def run(box):
    config = json.loads((box/'service.json').read_text())
    deployment = json.loads((box/'deployment.json').read_text())
    require = local.require
    results, cases = [], []
    save(box/'physical-start.json', {'at':time.time(),'scope':'real four-machine service; host reboot withheld for active shared calculations'})
    def passed(name):
        cases.append(name);save(box/'physical-tests.json',cases);print('PASS '+name,flush=True)
    def request():
        actor = 1 if len(results)<2 else 2
        db=sqlite3.connect(config['database'])
        row=db.execute('SELECT message FROM events WHERE id=?',(len(results)+1,)).fetchone();db.close()
        original=json.loads(row[0])['body']['request'] if row else None
        value = exchange(Path(config['pki'])/('auditor'+str(actor)),config['port'],config['source'],{'slots':63,'fields':3},expected_stream='recovery',lookup=original)
        if original and 'response' in value:value['request']=original
        if 'response' not in value:save(box/'physical-unconfirmed.json',value)
        require('response' in value,'source request did not complete: '+str(value.get('error')))
        results.append(value);save(box/'physical-responses.json',results)
        return value
    state = local.wait(box, lambda s:s['phase']=='ready' and not s['unavailable'])
    first = request();passed('four_physical_anchors_commit_a_new_original_Lean_service_event')
    # Only the authenticated SSH forwarding process belonging to this service.
    pid = state['processes']['c']['pid'];os.killpg(pid,signal.SIGKILL)
    local.wait(box,lambda s:s['phase']=='ready' and not s['unavailable'] and s['processes']['c']['pid']!=pid)
    request();passed('lost_SSH_tunnel_detected_rebuilt_and_service_continues')
    item = deployment['nodes']['c'];node=remote('c')
    before = json.loads(python(node,f"import json\nfrom pathlib import Path\nprint((Path({item['home']!r})/'status.json').read_text())"))
    body=verify(public_key(config['anchors']['trust']['members']['c']),'recovery-host-status',before)
    pid=body['process']['pid']
    code=f"import json,os,signal,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom recovery_loop import birth,boot_identity\np=Path({item['home']!r})/'state/anchor-process.json'\nr=json.loads(p.read_text());assert r['pid']=={pid} and r['boot']==boot_identity() and r['birth']==birth(r['pid'])\nos.killpg(r['pid'],signal.SIGKILL)\n"
    python(node,code)
    end=time.monotonic()+45
    while time.monotonic()<end:
        after=json.loads(python(node,f"from pathlib import Path\nprint((Path({item['home']!r})/'status.json').read_text())"))
        recovered=verify(public_key(config['anchors']['trust']['members']['c']),'recovery-host-status',after)
        if recovered['process']['pid']!=pid and time.time()-recovered['at']<8:break
        time.sleep(1)
    else:raise TimeoutError('remote OS-managed anchor was not rebuilt')
    local.wait(box,lambda s:s['phase']=='ready' and not s['unavailable'])
    save(box/'spark-process-recovery.json',{'before':before,'after':after})
    request();passed('physical_Spark_anchor_SIGKILL_OS_supervisor_rebuilds_same_identity_and_journal')
    unit='homework-public-anchor-recovery.service'
    before_pid=int(node.wsl('systemctl show --value -p MainPID '+unit+'\n',20,allow_probe=False))
    failed_at=time.time()
    node.wsl('sudo -n systemctl kill --kill-whom=main --signal=SIGKILL '+unit+'\n',20,allow_probe=False)
    end=time.monotonic()+40
    while time.monotonic()<end:
        after_pid=int(node.wsl('systemctl show --value -p MainPID '+unit+'\n',20,allow_probe=False))
        if after_pid and after_pid!=before_pid:break
        time.sleep(1)
    else:raise TimeoutError('systemd did not replace the crashed node supervisor')
    local.wait(box,lambda s:s['phase']=='ready' and not s['unavailable'] and s['at']>failed_at)
    save(box/'systemd-recovery.json',{'before_pid':before_pid,'after_pid':after_pid,'failed_at':failed_at})
    request();passed('physical_node_supervisor_crash_systemd_restarts_service')
    state=local.wait(box,lambda s:s['phase']=='ready' and not s['unavailable'])
    old=state['owner'];require(birth(old['pid'])==old['birth'],'stale coordinator identity')
    os.kill(old['pid'],signal.SIGKILL)
    request();passed('management_process_absent_original_service_still_generates_real_event')
    local.wait(box,lambda s:s['phase']=='ready' and s['owner']['pid']!=old['pid'] and not s['unavailable'],seconds=120)
    recovered=exchange(Path(config['pki'])/'auditor1',config['port'],config['source'],{},lookup=first['request'],expected_stream='recovery')
    require(recovered['response']['ledger']==first['response']['ledger'],'original request changed after automatic coordinator restart')
    passed('existing_ComputeNode_supervisor_automatically_restores_coordinator_and_original_lookup')
    # Read-only independent replay: no new request or source advancement.
    observed,head=replay(config,config['registry'])
    require(len(observed)==len(results)==5,'unexpected source event count')
    db=sqlite3.connect(config['database']);literal=db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall();db.close()
    evidence={}
    for member in 'bcd':
        item=deployment['nodes'][member]
        code = f"import json,sqlite3,hashlib\nfrom pathlib import Path\np=Path({item['home']!r})\ndb=sqlite3.connect('file:'+str(p/'journal.sqlite')+'?mode=ro',uri=True)\nr=db.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall();db.close()\n"
        code += "data={'rows':r,'status':json.loads((p/'status.json').read_text())}\n"
        code += f"data['protocol']={{n:hashlib.sha256((Path({item['code']!r})/n).read_bytes()).hexdigest() for n in {list(item['protocol'])!r}}}\nprint(json.dumps(data))"
        data=json.loads(python(remote(member),code));require([tuple(r[:4]) for r in data['rows']]==literal,'physical journal does not contain original source events')
        require(data['protocol']==item['protocol'],'deployed node source bytes changed')
        identity=config['anchors']['trust']['members'][member]
        status=verify(public_key(identity),'recovery-host-status',data['status'])
        require(status['source']==config['source'] and status['cluster']==digest(config['anchors']['trust']),'physical node scope changed')
        for seq,previous,hashed,text,signed in data['rows']:
            point=verify(public_key(identity),'anchor-commit',json.loads(signed))
            require(point['seq']==seq and point['head']==hashed and point['message']==digest(json.loads(text)),'physical original event signature differs')
        evidence[member]=data
    save(box/'physical-independent.json',evidence)
    passed('independent_original_source_replay_and_three_remote_signed_full_journals')
    save(box/'physical-acceptance.json',{'tests':cases,'source_events':5,'head':head,'labor':sum(int(x['labor']) for x in observed),
         'source':config['source'],'not_exercised':['physical hardware boot','cross-host writer election'],
         'scope':'four physical anchors; real original service; process/tunnel/OS-supervisor recovery'})
    print('PHYSICAL CONTINUOUS RECOVERY PASS: 7/7; five new source events; original lookup and cost preserved',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path);args=parser.parse_args();run(args.box.resolve())
