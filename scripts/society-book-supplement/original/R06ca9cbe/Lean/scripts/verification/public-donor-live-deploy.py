"""Stage the paid donor program and roll the original four HA participants."""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
import fcntl
import importlib.util
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from crypto import canonical,digest
from recovery_loop import save
import donor_arrival_admission as auth
import donor_arrival_live as donor
from donor_result_codec import PROFILE as RESULT_PROFILE


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


arrival=module('donor_original_roll','public-arrival-deploy.py')
actual=module('donor_original_actual','public-arrival-actual.py')
load,roll=arrival.load,arrival.roll


def execute(member,script,manifest,timeout=180):
    compile(script,'<donor-stage>','exec')
    if member=='a':
        return subprocess.check_output([sys.executable,'-B','-'],input=script,text=True,timeout=timeout)
    return arrival.execute(member,script,manifest,timeout)


def prepare(box,work,paid):
    manifest=load(box/'ha/deployment.json');config=load(box/'local-anchor/config.json')
    _,signed,prefix=auth.source_readiness.snapshot(config);rows=[list(r[:4]) for r in signed]
    certificate=dict(point=load(paid/'point.json'),votes=load(paid/'votes.json'),permission=load(paid/'owner-permit.json'))
    point=auth.permission(config,rows,certificate['point']['program'],certificate['votes'],certificate['permission'])
    assert prefix==point['prefix']
    privacy=box/'ha/regeneration/productive/external-arrival/online/donor-privacy/producer/independent.json'
    proof=load(privacy)
    assert proof['exit']==0 and proof['actual_producer_objects'] is True
    for name,h in certificate['votes']['a']['body']['objects'].items():
        assert proof['artifacts'][name[:-6].replace('/','.')] == h
    protocol={n:auth.sha(NETWORK/n) for n in sorted(set(manifest['protocol'])|
        {'donor_arrival_live.py','donor_arrival_admission.py','productive_owner_request.py','donor_result_codec.py'})}
    revision=digest(protocol);payload={n:base64.b64encode((NETWORK/n).read_bytes()).decode() for n in protocol}
    inventory=load(Path(config['arrival']['closure']));inventory.update(certificate['votes']['a']['body']['objects'])
    raw=canonical(inventory);(work/'closure.json').write_bytes(raw)
    descriptor=dict(source=point['source'],stream='recovery',compiler=point['program']['compiler'],
        source_root=auth.ORIGIN,facade='ExternalArrival.Donor.Wire.render',
        exporter_sha256=point['program']['sources'][auth.EXPORTER],closure_sha256=auth.sha(work/'closure.json'))
    if (work/'before.json').exists():assert load(work/'before.json')==manifest
    else:save(work/'before.json',manifest)
    save(work/'original.json',dict(prefix=prefix,rows=rows));save(work/'certificate.json',certificate)
    save(work/'paid-work.json',dict(directory=str(paid),point=digest(certificate['point']),input=auth.sha(paid/'request.json')))

    def stage(member):
        paid_record=load(paid/('node-'+member+'.json'));home=paid_record['home']+'/live'
        root=paid_record['home']+'/source';lib=paid_record['home']+'/lib'
        cfgpath=str(box/'local-anchor/config.json') if member=='a' else manifest['nodes'][member]['home']+'/config.json'
        code=str(NETWORK) if member=='a' else manifest['nodes'][member]['home']+'/code/'+revision+'/Verification/public-audit/network'
        oldcode=str(NETWORK) if member=='a' else manifest['nodes'][member]['code']
        script=f'''import base64,json,hashlib
from pathlib import Path
import sys
sys.path.insert(0,{oldcode!r})
import source_readiness
c=json.loads(Path({cfgpath!r}).read_text());me,signed,prefix=source_readiness.snapshot(c)
assert me=={member!r} and prefix=={prefix!r}
p=Path({home!r});p.mkdir(parents=True,exist_ok=True)
raw=base64.b64decode({base64.b64encode(raw).decode()!r});q=p/'closure.json'
if q.exists():assert q.read_bytes()==raw
else:q.write_bytes(raw)
for n,v in {payload!r}.items():
 q=Path({code!r})/n;raw=base64.b64decode(v);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==raw
 else:q.write_bytes(raw)
settings=dict(descriptor={descriptor!r},closure=str(p/'closure.json'),exporter={root+'/Lean/'+auth.EXPORTER!r},
 lean_path={lib!r},cwd={root+'/Lean'!r},backend=[c['arrival']['backend'][0],'--trust=0','-j1','--run',{root+'/Lean/'+auth.EXPORTER!r},'private-one'],
 error_log=str(p/'native.stderr'),native_call_seconds=300)
assert hashlib.sha256(Path(settings['exporter']).read_bytes()).hexdigest()==settings['descriptor']['exporter_sha256']
c.update(donor=settings,donor_admission={certificate!r})
c['semantic']['governance_context'].update(donor=settings,donor_admission={certificate!r})
q=p/'candidate.json';q.write_text(json.dumps(c))
sys.path.insert(0,{code!r});import donor_arrival_live
donor_arrival_live.certificate(c,[list(r[:4]) for r in signed])
donor_arrival_live.certificate(c['semantic']['governance_context'],[list(r[:4]) for r in signed])
print(json.dumps(dict(root={root!r},home={home!r},code={code!r},candidate=str(q),config=c)))
'''
        value=json.loads(execute(member,script,manifest,180));save(work/('staged-'+member+'.json'),value)
        print('DONOR LIVE SOURCE STAGED',member,flush=True);return member,value
    with ThreadPoolExecutor(max_workers=4) as pool:nodes=dict(pool.map(stage,'abcd'))
    save(work/'prepared.json',dict(nodes=nodes,protocol=protocol,revision=revision,descriptor=descriptor,privacy=auth.sha(privacy),prefix=prefix))


def install(box,work,paid):
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        prepared=load(work/'prepared.json');before=load(work/'before.json');original=load(work/'original.json')
        assert prepared['protocol']=={n:auth.sha(NETWORK/n) for n in prepared['protocol']}
        assert [list(r) for r in roll.spare.rows(before['mac']['service']['database'])]==original['rows']
        if (work/'installed.json').exists():
            assert load(box/'ha/deployment.json')['donor']['admission']==digest(load(work/'certificate.json'))
            print('PAID DONOR INSTALL RETAINED',flush=True);return
        manifest=deepcopy(before);configs={n:v['config'] for n,v in prepared['nodes'].items()};services={}
        for member in 'bcd':manifest['nodes'][member]['code']=prepared['nodes'][member]['code'];manifest['nodes'][member]['protocol']=prepared['protocol']
        inventory=load(work/'closure.json')
        for owner,member in [('mac','a'),('spark','c')]:
            cfg=deepcopy(before[owner]['service']);settings=configs[member]['donor'];entry=prepared['nodes'][member]
            cfg.update(donor=settings,donor_admission=load(work/'certificate.json'),
                       semantic=configs[member]['semantic'],streams=configs[member]['streams'],donor_result_codec=RESULT_PROFILE)
            assert donor.certificate(cfg,original['rows'])==load(work/'certificate.json')
            worker=dict(command=[settings['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',auth.EXPORTER,'public'],
                cwd=settings['cwd'],lean_path=settings['lean_path'],stderr=entry['home']+'/public.stderr',
                compiler_sha256=before[owner]['service']['online_privacy']['worker']['compiler_sha256'],contract='original77-donor-public/v1',timeout=300)
            inputs={settings['exporter']:settings['descriptor']['exporter_sha256'],settings['closure']:settings['descriptor']['closure_sha256']}
            inputs.update({settings['lean_path']+'/'+n:h for n,h in inventory.items()})
            cfg['online_privacy']={**cfg['online_privacy'],'worker':worker,'source_inputs':{**cfg['online_privacy']['source_inputs'],**inputs}}
            services[owner]=cfg
        progress=load(work/'install-progress.json') if (work/'install-progress.json').exists() else dict(stages=[])
        def done(name):
            if name not in progress['stages']:progress['stages'].append(name)
            save(work/'install-progress.json',progress);print('DONOR ROLL',name,flush=True)
        frozen=load(work/'writer-barrier.json') if (work/'writer-barrier.json').exists() else {}
        if (work/'install-failed.json').exists():
            frozen={}
        try:
            for owner in ('spark','mac'):
                if owner not in frozen:frozen[owner]=roll.freeze_writer(box,before,owner);save(work/'writer-barrier.json',frozen)
            from ha_quorum import Quorum
            end=time.monotonic()+30
            while True:
                states=Quorum(before['mac']['service']).collect('status')
                save(work/'barrier-status.json',states)
                if set(states)==set('abcd') and all(not v['intents'] and {k:v['head'][k] for k in ('seq','head')}==original['prefix'] for v in states.values()):break
                if time.monotonic()>=end:raise TimeoutError('DONOR_ROLL_BARRIER')
                time.sleep(.5)
            save(work/'barrier-status.json',states)
            for member in 'bcd':
                if 'anchor-'+member in progress['stages']:continue
                item=manifest['nodes'][member]
                execute(member,'from pathlib import Path\nPath('+repr(item['home']+'/config.json')+').write_text('+repr(json.dumps(configs[member]))+')',manifest,90)
                roll.restart_anchor(member,manifest)
                client=Quorum(before['mac']['service']).nodes[member];end=time.monotonic()+1800
                while time.monotonic()<end:
                    try:
                        state=client.call('semantic-status')
                        if state['prefix']==original['prefix'] and state['backend'] and not state['warm_error']:break
                    except (ValueError,OSError,EOFError):pass
                    time.sleep(2)
                else:raise TimeoutError('DONOR_VOTER_NOT_READY:'+member)
                done('anchor-'+member)
            save(box/'local-anchor/config.json',configs['a'])
            for owner in ('mac','spark'):
                manifest[owner]['service']=services[owner];manifest[owner]['controller']['release']=prepared['revision']
            for owner in ('spark','mac'):
                if 'candidate-'+owner in progress['stages']:continue
                arrival.prior.retire_writer(box,before,owner,frozen[owner])
                if owner=='spark':
                    item=manifest['nodes']['c'];command=[item['python'],item['code']+'/live_timing.py','coordinator',item['home']+'/ha/controller.json']
                    script=f'''from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'runtime/STOP').unlink(missing_ok=True)
(p/'service.json').write_text({json.dumps(services[owner])!r})
(p/'controller.json').write_text({json.dumps(manifest[owner]['controller'])!r})
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
'''
                    execute('c',script,manifest,90)
                    roll.spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
                else:
                    roll.module('donor_stop','public-recovery-isolation.py').stop(box)
                    save(box/'ha/mac/service.json',services[owner]);save(box/'ha/mac/controller.json',manifest[owner]['controller'])
                    (box/'runtime/STOP').unlink(missing_ok=True)
                    subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
                done('candidate-'+owner)
            manifest.update(protocol=prepared['protocol'],release=prepared['revision'],donor=dict(descriptor=prepared['descriptor'],evidence=str(work),admission=digest(load(work/'certificate.json'))))
            manifest['public_timing']['release']=prepared['revision'];manifest['application_receipts']['protocol']=prepared['protocol']
            for owner,member in [('mac','a'),('spark','c')]:manifest['application_receipts']['candidates'][owner]['code']=prepared['nodes'][member]['code']
            for member in 'abcd':manifest['semantic']['configurations'][member]=configs[member]['semantic']
            save(box/'ha/deployment.json',manifest)
            assert [list(r) for r in roll.spare.rows(manifest['mac']['service']['database'])]==original['rows']
            save(work/'installed.json',dict(prefix=original['prefix'],release=prepared['revision'],activated=False,stages=progress['stages']))
            print('DONOR INSTALLED; ORIGINAL77 UNCHANGED; CONTROL EVENT REQUIRED',flush=True)
        except BaseException:
            save(work/'install-failed.json',dict(stages=progress['stages'],at=time.time()))
            for owner,record in frozen.items():
                try:roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
                except (OSError,ValueError,RuntimeError,subprocess.SubprocessError):pass
            raise


def repair_context(box,work,paid):
    """Install the same original authority view in the two Handler contexts."""
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=load(box/'ha/deployment.json');rows=actual.continuous.rows(manifest)
        assert rows==load(work/'original.json')['rows'] and len(rows)==77
        prepared=load(work/'prepared.json');certificate=load(work/'certificate.json');fixed={};facts={}
        for owner,member in [('mac','a'),('spark','c')]:
            cfg=deepcopy(manifest[owner]['service']);anchor=prepared['nodes'][member]['config']
            cfg.update(semantic=anchor['semantic'],streams=anchor['streams'])
            code=prepared['nodes'][member]['code']
            script=f'''import json,sys
sys.path.insert(0,{code!r})
from donor_arrival_live import certificate
from ha_timing import public_configuration
from crypto import digest
c={cfg!r};r={rows!r}
assert certificate(c,r)=={certificate!r}
public_configuration(c)
print(json.dumps(dict(configuration=digest(c),certificate=digest(c['donor_admission']),native_computations=0)))
'''
            facts[owner]=json.loads(execute(member,script,manifest,180));fixed[owner]=cfg
            save(work/('context-service-'+owner+'.json'),cfg)
            print('ORIGINAL HANDLER CONTEXT VERIFIED',owner,flush=True)
        if (work/'context-installed.json').exists():
            assert all(manifest[o]['service']==fixed[o] for o in fixed)
            print('PAID CONTEXT INSTALL RETAINED',flush=True);return
        frozen={};stages=[]
        try:
            for owner in ('spark','mac'):
                frozen[owner]=roll.freeze_writer(box,manifest,owner);save(work/'context-barrier.json',frozen)
            for owner in ('mac','spark'):
                arrival.prior.retire_writer(box,manifest,owner,frozen[owner]);stages.append('retired-'+owner)
            item=manifest['nodes']['c']
            execute('c','from pathlib import Path\nPath('+repr(item['home']+'/ha/service.json')+').write_text('+repr(json.dumps(fixed['spark']))+')\nPath('+repr(item['home']+'/ha/runtime/STOP')+').unlink(missing_ok=True)',manifest,90)
            save(box/'ha/mac/service.json',fixed['mac'])
            for owner in fixed:manifest[owner]['service']=fixed[owner]
            save(box/'ha/deployment.json',manifest);stages.append('same-source-contexts-installed')
            roll.spare.transport.node('c').wsl('sudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
            # Let Spark acquire the existing fence before bringing Mac back as a candidate.
            end=time.monotonic()+90
            while time.monotonic()<end:
                state=actual.continuous.epoch.states(box,manifest)['spark']['body']
                if state.get('grant') and state['grant']['point']['owner']=='spark' and state['phase'] in {'recovering','leader'}:break
                time.sleep(1)
            else:raise TimeoutError('DONOR_CONTEXT_SPARK_FENCE_NOT_READY')
            stages.append('spark-original-fence')
            roll.module('donor_context_stop','public-recovery-isolation.py').stop(box)
            (box/'runtime/STOP').unlink(missing_ok=True)
            subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            stages.append('mac-candidate-started')
            save(work/'context-installed.json',dict(prefix=dict(seq=77,head=rows[-1][2]),contexts=facts,stages=stages,
                original_certificate=digest(certificate),native_computations=0,economic_requests=0,at=time.time()))
            print('ORIGINAL HANDLER CONTEXTS INSTALLED; SAME FOUR NATIVE OBJECTS AND OWNER PERMIT; JOURNAL77',flush=True)
        except BaseException:
            save(work/'context-failed.json',dict(stages=stages,at=time.time()))
            for owner in fixed:manifest[owner]['service']=fixed[owner]
            save(box/'ha/mac/service.json',fixed['mac'])
            item=manifest['nodes']['c']
            execute('c','from pathlib import Path\nPath('+repr(item['home']+'/ha/service.json')+').write_text('+repr(json.dumps(fixed['spark']))+')',manifest,90)
            save(box/'ha/deployment.json',manifest)
            actual.continuous.resume_runtime(box,manifest)
            raise


def install_codec(box,work,paid):
    """Roll the two public candidates; preserve native voters and committed IDs."""
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=load(box/'ha/deployment.json');rows=actual.continuous.rows(manifest)
        if (work/'codec-installed.json').exists():
            assert all(manifest[o]['service'].get('donor_result_codec')==RESULT_PROFILE for o in ('mac','spark'))
            print('PAID LOSSLESS CODEC INSTALL RETAINED',flush=True);return
        assert len(rows)==79 and rows[:77]==load(work/'original.json')['rows']
        assert json.loads(rows[-1][3])['body']['request']==load(work/'actual/donor-0-request.json')
        assert load(work/'codec-check.json')['exit']==0
        save(work/'codec-before.json',manifest);save(work/'codec-prefix.json',rows)
        protocol={n:auth.sha(NETWORK/n) for n in sorted(set(manifest['protocol'])|{'donor_result_codec.py'})}
        revision=digest(protocol);payload={n:base64.b64encode((NETWORK/n).read_bytes()).decode() for n in protocol}
        code=manifest['nodes']['c']['home']+'/code/'+revision+'/Verification/public-audit/network'
        script=f'''import base64,hashlib
from pathlib import Path
for n,v in {payload!r}.items():
 p=Path({code!r})/n;raw=base64.b64decode(v);p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
assert {{n:hashlib.sha256((Path({code!r})/n).read_bytes()).hexdigest() for n in {list(protocol)!r}}}=={protocol!r}
print('LOSSLESS_PUBLIC_CODE_STAGED')
'''
        assert execute('c',script,manifest,120).strip()=='LOSSLESS_PUBLIC_CODE_STAGED'
        codes={'mac':str(NETWORK),'spark':code};fixed={};contexts={}
        for owner,member in [('mac','a'),('spark','c')]:
            cfg=deepcopy(manifest[owner]['service']);cfg['donor_result_codec']=RESULT_PROFILE
            script=f'''import json,sys
sys.path.insert(0,{codes[owner]!r})
from ha_timing import public_configuration
from donor_arrival_live import certificate
from crypto import digest
c={cfg!r};public_configuration(c)
assert certificate(c,{rows!r})=={load(work/'certificate.json')!r}
print(json.dumps(dict(configuration=digest(c),native_computations=0)))
'''
            contexts[owner]=json.loads(execute(member,script,manifest,180));fixed[owner]=cfg
            print('LOSSLESS PUBLIC CONTEXT VERIFIED',owner,flush=True)
        save(work/'codec-prepared.json',dict(revision=revision,protocol=protocol,codes=codes,contexts=contexts))
        frozen={};stages=[]
        try:
            for owner in ('spark','mac'):
                frozen[owner]=roll.freeze_writer(box,manifest,owner);save(work/'codec-barrier.json',frozen)
            for owner in ('mac','spark'):
                arrival.prior.retire_writer(box,manifest,owner,frozen[owner]);stages.append('retired-'+owner)
            for owner in fixed:
                manifest[owner]['service']=fixed[owner];manifest[owner]['controller']['release']=revision
                manifest['application_receipts']['candidates'][owner]['code']=codes[owner]
            manifest.update(protocol=protocol,release=revision)
            manifest['public_timing']['release']=revision;manifest['application_receipts']['protocol']=protocol
            manifest['donor']['result_codec']=dict(profile=RESULT_PROFILE,public_code=codes,revision=revision)
            save(box/'ha/mac/service.json',fixed['mac']);save(box/'ha/mac/controller.json',manifest['mac']['controller'])
            item=manifest['nodes']['c'];command=[item['python'],code+'/live_timing.py','coordinator',item['home']+'/ha/controller.json']
            script=f'''from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'service.json').write_text({json.dumps(fixed['spark'])!r});(p/'controller.json').write_text({json.dumps(manifest['spark']['controller'])!r})
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if l.startswith('ExecStart=') else l for l in u.read_text().splitlines())+'\\n')
(p/'runtime/STOP').unlink(missing_ok=True)
'''
            execute('c',script,manifest,120);save(box/'ha/deployment.json',manifest)
            roll.spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
            end=time.monotonic()+90
            while time.monotonic()<end:
                state=actual.continuous.epoch.states(box,manifest)['spark']['body']
                if (state.get('configuration')==digest(manifest['spark']['controller']) and state.get('grant') and
                        state['grant']['point']['owner']=='spark' and state['phase'] in {'recovering','leader'}):break
                time.sleep(1)
            else:raise TimeoutError('DONOR_CODEC_SPARK_FENCE_NOT_READY')
            stages.append('spark-new-public-code')
            roll.module('donor_codec_stop','public-recovery-isolation.py').stop(box);(box/'runtime/STOP').unlink(missing_ok=True)
            subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            stages.append('mac-candidate-started')
            assert actual.continuous.rows(manifest)==rows
            save(work/'codec-installed.json',dict(prefix=dict(seq=79,head=rows[-1][2]),revision=revision,codes=codes,stages=stages,
                native_preparations=0,economic_requests=0,original_ids_preserved=True,at=time.time()))
            print('LOSSLESS PUBLIC CODEC INSTALLED; ORIGINAL79 AND REQUEST IDS PRESERVED; NATIVE VOTERS RETAINED',flush=True)
        except BaseException:
            save(work/'codec-failed.json',dict(stages=stages,at=time.time()))
            for owner,record in frozen.items():
                try:arrival.prior.retire_writer(box,manifest,owner,record)
                except Exception:pass
            actual.continuous.resume_runtime(box,manifest)
            raise


if __name__=='__main__':
    sys.dont_write_bytecode=True
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('operation',choices=['prepare','install','repair-context','install-codec']);p.add_argument('work',type=Path)
    p.add_argument('--box',type=Path,default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    p.add_argument('--admission-work',type=Path,default=Path('runtime/retained/iqa-actual77-donor-admission-20261106'))
    a=p.parse_args();globals()[a.operation.replace('-','_')](a.box.resolve(),a.work.resolve(),a.admission_work.resolve())
