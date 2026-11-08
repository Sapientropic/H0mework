"""Four-machine fault-domain exercise; no host reboot or shared network changes."""
from concurrent.futures import ThreadPoolExecutor
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import signal
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key
from challenge_anchor import QuorumClient
from client import exchange
from crypto import canonical, digest, verify
from exercise import replay
from quorum import verify_certificate
from quorum_exercise import Gate
from recovery_loop import birth, boot_identity, save

spec=importlib.util.spec_from_file_location('physical_recovery',Path(__file__).with_name('public-recovery-physical.py'))
physical=importlib.util.module_from_spec(spec);spec.loader.exec_module(physical)
wait=physical.local.wait
require=physical.local.require


def rows(box):
    db=sqlite3.connect('file:'+str(box/'service.sqlite')+'?mode=ro',uri=True)
    try:return db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
    finally:db.close()


def stop(box):
    state=box/'runtime';(state/'STOP').touch()
    end=time.monotonic()+90
    while (state/'supervisor.pid').exists() and time.monotonic()<end:time.sleep(.2)
    require(not (state/'supervisor.pid').exists(),'owned supervisor did not finish stopping')


def configure(box,loop,service,label):
    save(box/'loop.json',loop);save(box/'service.json',service)
    binding=box/'runtime/binding.json'
    if binding.exists():binding.rename(box/'runtime'/('binding-'+label+'.json'))


def start(box):
    state=ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'
    subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(state),sys.executable,'-u',
                    str(NETWORK/'recovery_loop.py'),str(box/'loop.json')],cwd=ROOT,check=True,capture_output=True)


def kill_record(record):
    require(record['boot']==boot_identity() and birth(record['pid'])==record['birth']
            and os.getpgid(record['pid'])==record['pgid']==record['pid'],'process ownership changed')
    os.killpg(record['pid'],signal.SIGKILL)


def run(box):
    original_loop=json.loads((box/'loop.json').read_text())
    original_service=json.loads((box/'service.json').read_text())
    base=rows(box);require(len(base)==5,'explicit original five-event baseline required')
    gates={};cases=[];source_key=public_key(original_service['registry']['server']);frozen_owner=None
    def passed(name):
        cases.append(name);save(box/'isolation-tests.json',cases);print('PASS '+name,flush=True)
    save(box/'isolation-baseline.json',{'rows':base,'loop':original_loop,'service':original_service,'boot':boot_identity()})
    stop(box)
    try:
        config=copy.deepcopy(original_service);loop=copy.deepcopy(original_loop)
        for member in 'bcd':
            gates[member]=Gate(config['anchors']['endpoints'][member]['port'])
            config['anchors']['endpoints'][member]['port']=gates[member].port
        loop['service_entrypoint']=str(NETWORK/'recovery_fault_service.py')
        save(box/'isolation-configuration.json',{'loop':loop,'service':config})
        configure(box,loop,config,'before-isolation');start(box)
        state=wait(box,lambda s:s['phase']=='ready' and not s['unavailable'])
        require(rows(box)==base,'routing update changed an original event')
        passed('explicit_fault_runner_uses_original_service_with_unchanged_source_membership_and_prefix')
        save(box/'fault-armed.json',{'phase':'after-original-quorum-before-local-commit'})
        with ThreadPoolExecutor(max_workers=1) as worker:
            future=worker.submit(exchange,Path(config['pki'])/'auditor2',config['port'],config['source'],
                                 {'slots':63,'fields':3},expected_stream='recovery')
            end=time.monotonic()+45
            while not (box/'fault-boundary.json').exists() and time.monotonic()<end:
                if future.done():
                    try:value=future.result()
                    except Exception as error:value={'error':repr(error)}
                    save(box/'isolation-before-boundary-failure.json',value)
                    break
                time.sleep(.05)
            require((box/'fault-boundary.json').exists(),'original commit boundary was not reached')
            boundary=verify(source_key,'recovery-fault-boundary',json.loads((box/'fault-boundary.json').read_text()))
            # Freeze this task's manager before its health timeout can dispose
            # the deliberately stopped source process or replace its records.
            owner=state['owner'];require(birth(owner['pid'])==owner['birth'],'stale loop owner')
            os.kill(owner['pid'],signal.SIGSTOP);frozen_owner=owner
            groups={name:json.loads((box/'runtime'/(name+'-process.json')).read_text())
                    for name in ['service','member-a','member-b','member-c','member-d']}
            pending=(box/'service.sqlite.pending.json').read_bytes();intent=json.loads(pending)
            require(intent=={k:boundary[k] for k in ('seq','previous','message')} and intent['seq']==6,'pending is not the exact generated event')
            point=verify_certificate(config['anchors']['trust'],boundary['receipt'],source=config['source'],stream='recovery',
                  seq=6,head=boundary['receipt']['body']['head'],previous=boundary['previous'],message=boundary['message'])
            require(rows(box)==base,'uncommitted local event was published early')
            save(box/'isolation-pending.json',intent)
            passed('real_quorum_commit_precedes_local_commit_with_exact_durable_original_intent')
            for gate in gates.values():gate.blocked=True
            cuts={}
            for name,node in QuorumClient(config).nodes.items():
                try:cuts[name]=node.head()
                except (OSError,EOFError,ValueError) as error:cuts[name]={'error':type(error).__name__}
            require(all('error' in cuts[name] for name in 'bcd') and cuts['a']['seq']==6,'coordinator data paths were not actually cut')
            save(box/'isolated-links.json',cuts)
            passed('coordinator_isolated_from_all_three_remote_data_paths_with_management_plane_preserved')
            # The independent fault injector and outer OS supervisor stay alive.
            # Every recorded application group, including source and tunnels,
            # is cold-started; no unrelated PID or system service is touched.
            killed={}
            for name,record in groups.items():
                kill_record(record);killed[name]=record
            os.kill(owner['pid'],signal.SIGKILL);frozen_owner=None
            save(box/'cold-start-groups.json',{'owner':owner,'groups':killed})
            result=future.result(timeout=40)
            require(result.get('error')=='OUTCOME_UNKNOWN' and result['request']==boundary['message']['body']['request'],
                    'client uncertainty lost the original request identity')
            save(box/'isolation-unknown.json',result)
        blocked=wait(box,lambda s:s['phase']=='blocked' and s['owner']['pid']!=owner['pid'],seconds=180)
        require(blocked['unavailable']==list('bcd') and blocked['members']['a']==
                {key:point[key] for key in ('source','stream','seq','head')} and
                blocked['processes']['service'] is None and 'QUORUM_UNAVAILABLE' in blocked['error'],
                'cold restart did not block on the exact isolated remote quorum')
        require(rows(box)==base and (box/'service.sqlite.pending.json').read_bytes()==pending,'cold isolation changed durable data')
        save(box/'cold-isolated-status.json',json.loads((box/'runtime/status.json').read_text()))
        require(all(gate.refused>0 for gate in gates.values()),'a remote link was never exercised while cut')
        passed('all_owned_application_groups_cold_start_under_total_remote_isolation_without_new_genesis')
        for gate in gates.values():gate.blocked=False
        restored=wait(box,lambda s:s['phase']=='ready' and not s['unavailable'] and s['head']['seq']==6,seconds=120)
        require(len(rows(box))==6 and json.loads(rows(box)[-1][3])==intent['message'],'recovery replaced the pending original event')
        original=intent['message']['body']['request']
        recovered=exchange(Path(config['pki'])/'auditor2',config['port'],config['source'],{},lookup=original,expected_stream='recovery')
        require(recovered['response']['ledger']==intent['message'] and recovered['response']['anchor']['body']==point,
                'lookup changed the original externally committed result')
        save(box/'isolation-recovered.json',recovered)
        passed('reconnected_quorum_automatically_recovers_the_exact_original_request_without_repayment')
        next_result=exchange(Path(config['pki'])/'auditor2',config['port'],config['source'],{'slots':63,'fields':3},expected_stream='recovery')
        require('response' in next_result and next_result['response']['anchor']['body']['seq']==7,'recovered service did not generate its next event')
        save(box/'isolation-next.json',next_result)
        passed('recovered_original_service_generates_and_commits_its_own_next_event')
        save(box/'isolation-gates.json',{name:{'refused':gate.refused,'accepted':gate.connections} for name,gate in gates.items()})
    finally:
        if frozen_owner and birth(frozen_owner['pid'])==frozen_owner['birth']:
            os.kill(frozen_owner['pid'],signal.SIGCONT)
        for gate in gates.values():gate.blocked=False
        try:
            stop(box)
        except Exception as error:
            # Keep working transport and the saved configuration if the owner
            # cannot be stopped; never launch a competing writer.
            save(box/'isolation-cleanup-failure.json',{'error':repr(error)})
            raise
        finally:
            try:configure(box,original_loop,original_service,'after-isolation')
            finally:
                for gate in gates.values():gate.close()
                if not (box/'runtime/supervisor.pid').exists():start(box)
    wait(box,lambda s:s['phase']=='ready' and not s['unavailable'] and s['head']['seq']==7)
    require(boot_identity()==json.loads((box/'isolation-baseline.json').read_text())['boot'],'physical host was restarted')
    records,head=replay(original_service,original_service['registry'])
    require(len(records)==7 and sum(int(x['labor']) for x in records)==12,'original source replay or payment differs')
    final=rows(box);evidence={}
    deployment=json.loads((box/'deployment.json').read_text())
    for member in 'bcd':
        item=deployment['nodes'][member]
        code=f"import json,sqlite3\nfrom pathlib import Path\np=Path({item['home']!r});d=sqlite3.connect('file:'+str(p/'journal.sqlite')+'?mode=ro',uri=True)\nr=d.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall();d.close()\nprint(json.dumps({{'rows':r,'status':json.loads((p/'status.json').read_text())}}))"
        value=json.loads(physical.python(physical.remote(member),code))
        require([tuple(row[:4]) for row in value['rows']]==final,'physical replica did not receive the exact final source history')
        identity=config['anchors']['trust']['members'][member]
        for seq,previous,hashed,text,signed in value['rows']:
            receipt=verify(public_key(identity),'anchor-commit',json.loads(signed))
            require(receipt['source']==config['source'] and receipt['seq']==seq and receipt['head']==hashed
                    and receipt['message']==digest(json.loads(text)),'replica signature/source mismatch')
        current=verify(public_key(identity),'recovery-host-status',value['status'])
        prior=verify(public_key(identity),'recovery-host-status',json.loads((box/'physical-independent.json').read_text())[member]['status'])
        require(current['boot']==prior['boot'],'a remote physical host restarted during isolated tests')
        evidence[member]=value
    save(box/'isolation-independent.json',evidence)
    passed('independent_source_and_all_physical_journals_agree_cost_12_and_all_host_boots_unchanged')
    save(box/'isolation-acceptance.json',{'tests':cases,'source_events':7,'labor':12,'head':head,'physical_host_reboots':0,
         'scope':'application cold restart; coordinator data-path loss; committed-event uncertainty; automatic recovery',
         'hardware_power_loss':False,'cross_host_writer_election':False})
    print(f'ISOLATED FAULT-DOMAIN RECOVERY PASS: {len(cases)}/{len(cases)}; 7 source events; labor 12; zero physical host reboots',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path);args=parser.parse_args();run(args.box.resolve())
