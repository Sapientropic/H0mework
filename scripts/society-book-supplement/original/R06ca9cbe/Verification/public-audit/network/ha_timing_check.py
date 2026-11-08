"""Independent timing/frame consumer. Private replay starts only after public exit."""
from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import sqlite3
import subprocess
import sys
import time

from online_privacy_check import source_request, wire_observations, tls_streams
from privacy_compare import canonical, digest, public_keys, signed
from quorum import verify_certificate
from recovery_loop import birth

ROOT=Path(__file__).resolve().parents[3]
MODULE='SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Privacy/'
MOUTHS=('Timing.rebuild_twin','Timing.rebuild_from_twin','Timing.initial_private_frame_is_exact',
    'Timing.rebuild_commutes_with_actual_next','Timing.handoff_rebuild_is_own_current',
    'Timing.handoff_rebuild_is_own_root_next','Timing.all_private_frames_have_the_same_complete_timed_observation',
    'Timing.framed_public_run_is_actual',
    'Timing.original_source_generates_related_handoff_seeds','Timing.public_next_with_generated_frame_is_actual_root_next',
    'initial_windows_are_generated','handoff_keeps_own_private_feed',
    'Network.all_exogenous_laws_preserve_complete_observation_distribution','Network.independent_draws_have_the_same_product_law')


def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(path,value):Path(path).write_bytes(canonical(value)+b'\n')


def no_private(value):
    if isinstance(value,dict):
        assert not {'private_variant','private_exporter','private_journal','own_frame','__private_audit'}.intersection(value)
        for item in value.values():no_private(item)
    elif isinstance(value,list):
        for item in value:no_private(item)
    else:assert value!='private-two'


def audit(run,out):
    audit_source=sha(__file__)
    out.mkdir(parents=True,exist_ok=False)
    receipt=load(run/'accepted.json')
    for path,wanted in receipt['source_inputs'].items():assert sha(path)==wanted,('PUBLIC_EXECUTED_SOURCE',path)
    for path,wanted in receipt['files'].items():assert sha(run/path)==wanted,('ACTUAL_BYTES',path)
    prefix=load(run/'original-prefix.json');assert len(prefix)==24
    baseline=Path(receipt['baseline']);base=load(baseline/'actual/one/config.json')
    accepted_base=load(baseline/'actual/accepted.json')
    for path,wanted in accepted_base['source_inputs'].items():assert sha(path)==wanted
    for path,wanted in accepted_base['files'].items():assert sha(baseline/'actual'/path)==wanted
    source_base=load(Path(accepted_base['baseline'])/'accepted.json')
    module_hashes={**source_base['compiled_modules'],**load(baseline/'build.json')['modules']}
    for name,wanted in module_hashes.items():
        for library in (Path(base['worker']['lean_path']),run.parent/'lib'):
            assert sha(library/(MODULE+name+'.olean'))==wanted,('PAID_MODULE_BINDING',name,str(library))
    lean=base['worker']['command'][0];assert sha(lean)==base['descriptor']['compiler_sha256']
    env=os.environ.copy();env['LEAN_PATH']=base['worker']['lean_path']
    metadata={};source_configs={};all_processes=[];last_response=0
    checked_artifacts=set();native_pairs={};source_inputs={}
    for lane in ('one','two'):
        directory=run/lane;cfg=load(directory/'config.json');no_private(cfg)
        assert cfg['public_representative']=='original-fixed-source/v1'
        assert cfg['backend']==cfg['public_base_source']['backend']
        assert cfg['lean_path']==cfg['public_base_source']['lean_path']
        assert cfg['online_privacy']['worker']['lean_path']==base['worker']['lean_path']
        assert cfg['backend'][-1]=='private-one'
        assert Path(cfg['backend'][0]).resolve()==Path(lean).resolve()
        source_configs[lane]=cfg
        public=public_keys(directory/'public')
        settings=[cfg['public_base_source'],*(cfg[name] for name in ('governance','energy','continuation','handoff'))]
        for member in 'abcd':
            ac=load(directory/(member+'-config.json'));no_private(ac)
            settings.append(ac['semantic'])
            settings.extend(ac['semantic']['governance_context'][name] for name in ('governance','energy','continuation','handoff'))
            assert ac['public_representative']==cfg['public_representative']
            assert ac['semantic']['backend'][-1]=='private-one'
        allowed={tuple(cfg['backend']),tuple(cfg['online_privacy']['worker']['command'])}
        for item in settings:
            assert len(item['backend'])==6 and item['backend'][1:4]==['--trust=0','-j1','--run'] and item['backend'][-1]=='private-one'
            assert Path(item['backend'][4]).resolve()==Path(item['exporter']).resolve()
            assert sha(item['exporter'])==item['descriptor']['exporter_sha256']
            assert sha(item['closure'])==item['descriptor']['closure_sha256']
            key=(item['lean_path'],item['descriptor']['closure_sha256'])
            if key not in checked_artifacts:
                for name,wanted in load(item['closure']).items():assert sha(Path(item['lean_path'])/name)==wanted
                checked_artifacts.add(key)
            allowed.add(tuple(item['backend']))
        snapshots=load(directory/'public-processes.json')
        assert [item['phase'] for item in snapshots]==['before-request','after-paid-reply','durable-intent','after-recovery-and-next']
        seen=set()
        for sample in snapshots:
            for process in sample['processes']:
                args=shlex.split(process['command'])
                assert 'private-two' not in args and '__private_audit' not in process['command']
                assert str(run/'owner-private') not in process['command']
                if Path(args[0]).name=='lean':
                    assert tuple(args) in allowed or args==[lean,'--githash'],('ACTUAL_PUBLIC_ARGV',args)
                    seen.add(tuple(args))
                all_processes.append(process)
        assert tuple(cfg['backend']) in seen and tuple(cfg['handoff']['backend']) in seen
        # Validate the actual sandbox argv, then independently exercise exactly that policy.
        ready=load(directory/'writer-1-ready.json');launch=ready['launcher_argv']
        assert launch[:2]==['/usr/bin/sandbox-exec','-p'] and launch[-2]=='writer'
        denied=[run/'owner-private',Path(cfg['original_live_root']).parent/'privacy/online-01/exporters-01']
        expected='(version 1)(allow default)'+''.join('(deny file-read* file-write* (subpath '+json.dumps(str(path.resolve()))+'))' for path in denied)
        assert launch[2]==expected
        probe='import pathlib,sys\nfor name in sys.argv[1:]:\n try:pathlib.Path(name).read_bytes()\n except PermissionError:continue\n raise RuntimeError("PRIVATE_FILE_READABLE")\nprint("PRIVATE_FILES_DENIED")\n'
        checked=subprocess.run(launch[:3]+[sys.executable,'-c',probe,str(run/'owner-private/one.json'),str(run/'owner-private/two.json')],text=True,capture_output=True,timeout=10)
        assert checked.returncode==0 and checked.stdout.strip()=='PRIVATE_FILES_DENIED',checked.stderr
        (out/(lane+'-isolation.log')).write_text(checked.stdout+checked.stderr)
        events=load(directory/'events.json');assert len(events)==27 and events[:24]==prefix
        originals=load(Path(cfg['original_live_root'])/'service.json')
        with sqlite3.connect(Path(originals['database']).as_uri()+'?mode=ro',uri=True) as db:
            original_rows=db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
        assert len(original_rows)==27 and [list(row) for row in original_rows[:24]]==prefix
        assert original_rows[-1][2]==receipt['original_live_head']
        trust=load(directory/'trust.json');boundaries,wires=wire_observations(directory/'boundary.jsonl',public)
        observations=load(directory/'observations.json');assert len(observations)==6 and len(wires)==5
        replies=[]
        for index,message in enumerate(observations):
            actor=message['body']['request']['body']['actor'];key=public['auditor'+actor]['app']
            observed=signed(key,'online-client-observation',message)
            request=observed['request'];challenge=signed(public['server']['app'],'challenge',observed['challenge'])
            body=signed(key,request['kind'],request)
            for field in ('source','stream','actor','nonce','seq','cut','epoch','expires'):assert body[field]==challenge[field]
            clocks=[observed['times'][field] for field in ('connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns')]
            assert clocks==sorted(clocks) and all(type(t) is int for t in clocks)
            last_response=max(last_response,clocks[-1])
            response=observed['response']
            if index==2:
                assert response.get('transport_error') in {'EOFError','ConnectionResetError'}
                assert observed['tls'] in {'TLSv1.3',None}
                continue
            assert observed['tls']=='TLSv1.3'
            rb=signed(public['server']['app'],response['kind'],response)
            result=rb['result'] if response['kind']=='lookup-response' else rb
            if response['kind']=='lookup-response':assert rb['request']==digest(request)
            row=events[result['anchor']['body']['seq']-1]
            assert result['ledger']==json.loads(row[3])
            event=signed(public['server']['app'],'ledger',result['ledger'])
            assert result['event']==event and set(event)=={'type','source','stream','request','peer','scope','native','nextScope'}
            assert result['head']==row[2]==hashlib.sha256(bytes.fromhex(row[1])+canonical(result['ledger'])).hexdigest()
            verify_certificate(trust,result['anchor'],source=cfg['source'],stream=cfg['stream'],seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
            assert result['request']==digest(event['request'])
            wire,wc,wr,ws=wires[len(replies)]
            assert (wc,wr,ws)==(observed['challenge'],request,response)
            assert wire['started_ns']<=clocks[-1] and wire['finished_ns']>=clocks[3]
            replies.append(result)
        assert replies[0]==replies[1] and replies[2]==replies[3]
        pending=load(directory/'pending.json')
        assert pending['seq']==26 and pending['message']==json.loads(events[25][3])
        assert pending['message']['body']['request']==observations[2]['body']['request']
        fault=signed(public['server']['app'],'ha-fault-boundary',load(directory/'ha-fault-boundary.json'))
        assert fault['seq']==26 and fault['message']==pending['message'] and fault['phase']=='after-intent'
        phases={(item['seq'],item['phase']) for item in boundaries}
        assert {(25,'before-intent'),(26,'before-intent'),(26,'before-reconcile'),(26,'restore'),(27,'before-intent')}<=phases
        inputs=[];values=[]
        for seq in (25,26,27):
            raw=source_request(events[:seq]);event=json.loads(events[seq-1][3])['body'];inputs.append(raw);values.append(event['native'])
            relevant=[item for item in boundaries if item['seq']==seq]
            assert relevant and all(item['input']==raw and item['event']==digest(event) and item['native']==digest(event['native']) for item in relevant)
        assert [item['reason'] for item in values]==['DELIVERED','UNAUTHORIZED','UNFUNDED']
        assert values[0]['before']['energy']==['2','0','0','3'] and values[0]['next']['energy']==['0']*4
        assert values[0]['next']==values[1]['before'] and values[1]['next']==values[2]['before']
        assert all(not row['accepted'] for item in values[1:] for row in item['rows'])
        assert len({json.loads(row[3])['body']['request']['body']['request_id'] for row in events})==27
        metadata[lane]={'tls_streams':tls_streams(directory),'raw_observations':len(observations)}
        native_pairs[lane]=values;source_inputs[lane]=inputs
    assert native_pairs['one']==native_pairs['two']
    # Do not trust the producer's empty-list marker: inspect every observed owned PID now.
    alive=[]
    for process in all_processes:
        if process['birth'] and birth(process['pid'])==process['birth']:alive.append(process)
    assert not alive,('PUBLIC_EPOCH_NOT_CLOSED',alive)
    closed_at=time.monotonic_ns();assert closed_at>last_response
    save(out/'private-audit-start.json',{'at_ns':closed_at,'last_application_response_ns':last_response,
        'observed_public_processes':len({p['pid'] for p in all_processes}),'remaining':alive,
        'actual_receipt_sha256':sha(run/'accepted.json')})
    # Independent fresh strict builds, retaining shared paid dependencies.
    library=out/'lib';library.mkdir()
    prior=run.parent/'lib'
    for dependency in prior.rglob('*'):
        target=library/dependency.relative_to(prior)
        if dependency.is_dir():target.mkdir(exist_ok=True)
        elif dependency.name.endswith('.olean') and dependency.relative_to(prior).as_posix() in {MODULE+'Timing.olean',MODULE+'Timing/Source.olean'}:
            continue
        else:os.link(dependency,target)
    env['LEAN_PATH']=str(library)
    for name in ('Timing','Timing/Source'):
        source=ROOT/'Lean'/(MODULE+name+'.lean');target=library/(MODULE+name+'.olean');target.parent.mkdir(exist_ok=True)
        result=subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','-o',str(target),str(source)],cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=120)
        (out/(name.replace('/','-')+'.log')).write_text(result.stdout+result.stderr)
        assert result.returncode==0,result.stdout+result.stderr
        assert sha(target)==sha(prior/(MODULE+name+'.olean'))
    namespace=MODULE.replace('/','.')
    capsule=out/'kernel.lean';capsule.write_text('import '+namespace+'Timing.Source\n'+''.join('#print axioms '+namespace+name+'\n' for name in MOUTHS))
    checked=subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',str(capsule)],cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=120)
    (out/'kernel.log').write_text(checked.stdout+checked.stderr);assert checked.returncode==0,checked.stdout+checked.stderr
    mouths=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",checked.stdout)
    assert {name for name,_ in mouths}=={namespace+name for name in MOUTHS}
    for _,axioms in mouths:assert set(filter(None,map(str.strip,axioms.split(','))))<={'propext','Classical.choice','Quot.sound'}
    owner_source=ROOT/'Lean/scripts/verification/ha-timing-owner-source.lean'
    checked=subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',str(owner_source)],cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=120)
    (out/'owner-build.log').write_text(checked.stdout+checked.stderr);assert checked.returncode==0,checked.stdout+checked.stderr
    private_results={}
    for lane in ('one','two'):
        owned=load(run/'owner-private'/(lane+'.json'))
        assert set(owned)=={'source','prefix','original_source_argument','frame_definition','source_family_receipt'}
        assert owned['source']==source_configs[lane]['source'] and owned['prefix']=={'seq':24,'head':prefix[-1][2]}
        assert owned['frame_definition']=='Timing.ownFrame ownSeed.window.initial'
        assert owned['source_family_receipt']==sha(run.parent.parent/'accepted-03/accepted.json')
        variant='private-two' if owned['original_source_argument'] else 'private-one'
        assert variant==('private-one' if lane=='one' else 'private-two')
        command=[lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',str(owner_source),variant]
        started=time.monotonic_ns();assert started>=closed_at
        result=subprocess.run(command,cwd=ROOT/'Lean',env=env,text=True,capture_output=True,
            input=''.join(canonical(item).decode()+'\n' for item in source_inputs[lane]),timeout=120)
        (out/(lane+'-owner.stdout')).write_text(result.stdout)
        assert result.returncode==0 and not result.stderr,result.stderr
        answers=[json.loads(line) for line in result.stdout.splitlines()];assert len(answers)==3
        for index,answer in enumerate(answers):
            assert answer['native']==native_pairs[lane][index]
            assert answer['actualPublic']==answer['rebuiltPublic']==answer['native']['next']
            assert answer['consumedRequests']==index+1
            for item in answer['frame']:assert item['sourceInitial']==item['actualNext']==item['rebuiltNext']
            assert answer['frame'][3]['actualNext']==('39' if lane=='one' else '38')
        private_results[lane]={'argv':command,'started_ns':started,'finished_ns':time.monotonic_ns(),
            'source_sha256':sha(owner_source),'output_sha256':sha(out/(lane+'-owner.stdout')),
            'own_feed':answers[-1]['frame'][3]['actualNext'],'actual_nexts':3}
    save(out/'private-materialization.json',private_results)
    # Exercise actual startup rejection before it can open a listener or a private file.
    negatives=[]
    for name in ('base-private','nested-private','own-frame','base-argv'):
        bad=copy.deepcopy(source_configs['one'])
        if name=='base-private':bad['backend'][-1]='private-two'
        elif name=='nested-private':bad['handoff']['private_variant']='private-one'
        elif name=='own-frame':bad['own_frame']={'feed':'39'}
        else:bad['backend'][4]=bad['handoff']['exporter']
        path=out/(name+'.json');save(path,bad)
        result=subprocess.run([sys.executable,str(ROOT/'Verification/public-audit/network/ha_timing.py'),'writer',str(path)],text=True,capture_output=True,timeout=15)
        (out/(name+'.log')).write_text(result.stdout+result.stderr)
        assert result.returncode!=0 and not result.stdout and any(code in result.stderr for code in
            ('PRIVATE_SELECTOR_ON_PUBLIC_PATH','PRIVATE_INPUT_ON_PUBLIC_PATH','PUBLIC_BASE_SOURCE_ARGV'))
        negatives.append(name)
    save(out/'tls-streams.json',metadata)
    assert sha(__file__)==audit_source,'AUDIT_SOURCE_CHANGED_DURING_RUN'
    result={'actual_receipt_sha256':sha(run/'accepted.json'),'audit_source_sha256':audit_source,
        'proof_sources':{name:sha(ROOT/'Lean'/(MODULE+name+'.lean')) for name in ('Timing','Timing/Source')},
        'owner_source_sha256':sha(owner_source),'standard_axiom_mouths':len(mouths),
        'public_epochs':2,'public_private_replay_calls':0,'closed_processes_checked':len({p['pid'] for p in all_processes}),
        'private_frames_generated_from_original_source':['39','38'],'whole_state_rebuild':True,
        'late_actual_next_materializations':6,'original_events':27,'paid_energy_each':5,
        'pending_recoveries':2,'no_repayment':True,'tls_streams':24,'complete_application_connections':10,
        'startup_negatives':negatives,'raw_clocks_retained':True,
        'scope':'HA complete timed observation has no private frame argument under the common exogenous entropy/scheduler law; no concurrent private replay in the public epoch; exact whole own-root next reconstructed, not deferred'}
    save(out/'accepted.json',result)
    print('INDEPENDENT HA TIMING PASS: 2 public epochs; 0 private replay calls; exact whole-state/own-root reconstruction; late feed39/38; pending recovery/no repayment; 24 TLS streams; 4 startup rejections',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);p.add_argument('out',type=Path)
    args=p.parse_args();audit(args.run.resolve(),args.out.resolve())
