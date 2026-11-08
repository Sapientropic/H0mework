"""Roll only the original writer candidates onto durable application receipts."""
import argparse,base64,copy,fcntl,importlib.util,json,shlex,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from crypto import digest
from recovery_loop import save

def module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
deploy=module('application_deploy','public-supply-deploy.py');roll=deploy.roll;load=deploy.load

def install(box):
    lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=box/'ha/regeneration/online/applications';home.mkdir(exist_ok=True)
    current=load(box/'ha/deployment.json')
    if (home/'installed.json').exists():
        value=load(home/'installed.json');assert current['application_receipts']['release']==value['release']
        print('APPLICATION RECEIPT ROLL RETAINED');return
    if not (home/'before.json').exists():save(home/'before.json',current)
    before=load(home/'before.json');manifest=copy.deepcopy(before)
    literal=roll.spare.rows(before['mac']['service']['database'])
    assert len(literal)==45
    names=sorted(set(before['protocol'])|{'application_receipts.py'})
    protocol={name:deploy.sha(NETWORK/name) for name in names};revision=digest(protocol)
    progress=load(home/'roll-progress.json') if (home/'roll-progress.json').exists() else {'stages':[]}
    def paid(stage):
        if stage not in progress['stages']:progress['stages'].append(stage)
        save(home/'roll-progress.json',progress);print('APPLICATION ROLL',stage,flush=True)
    item=before['nodes']['c'];codepath=item['home']+'/code/'+revision+'/Verification/public-audit/network'
    if 'staged' not in progress['stages']:
        payload={n:base64.b64encode((NETWORK/n).read_bytes()).decode() for n in names}
        code=f'''import base64,hashlib,sys
from pathlib import Path
p=Path({codepath!r});p.mkdir(parents=True,exist_ok=True)
for n,v in {payload!r}.items():
 raw=base64.b64decode(v);assert hashlib.sha256(raw).hexdigest()=={protocol!r}[n]
 f=p/n
 if f.exists():assert f.read_bytes()==raw
 else:f.write_bytes(raw)
sys.path.insert(0,str(p))
from application_receipts import Journal
from online_privacy import Handler
print('APPLICATION_RELEASE_IMPORT_PASS')
'''
        deploy.execute('c',code,before,60);paid('staged')
    if 'barrier' not in progress['stages']:
        frozen={}
        try:
            for owner in ('spark','mac'):
                frozen[owner]=roll.freeze_writer(box,before,owner);save(home/'barrier.json',frozen)
            from ha_quorum import Quorum
            end=time.monotonic()+30
            while True:
                states=Quorum(before['mac']['service']).collect('status')
                if len(states)>=3 and all(v['head']['seq']==45 and not v['intents'] for v in states.values()):break
                if time.monotonic()>=end:
                    save(home/'barrier-incomplete.json',states);raise ValueError('APPLICATION_ROLL_BARRIER')
                time.sleep(.5)
            paid('barrier')
        except BaseException:
            for owner,record in frozen.items():roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            raise
    frozen=load(home/'barrier.json')
    for owner in ('mac','spark'):manifest[owner]['controller']['release']=revision
    try:
        for owner in ('spark','mac'):
            if owner in progress['stages']:continue
            deploy.retire_writer(box,before,owner,frozen[owner])
            if owner=='spark':
                command=[item['python'],codepath+'/live_timing.py','coordinator',item['home']+'/ha/controller.json']
                script=f'''from pathlib import Path
p=Path({item['home']+'/ha'!r});(p/'runtime/STOP').unlink(missing_ok=True)
(p/'controller.json').write_text({json.dumps(manifest[owner]['controller'])!r}+'\\n')
u=p/'ha.service';u.write_text('\\n'.join('ExecStart='+{shlex.join(command)!r} if s.startswith('ExecStart=') else s for s in u.read_text().splitlines())+'\\n')
'''
                deploy.execute('c',script,before,60)
                roll.spare.transport.node('c').wsl('sudo -n install -m 644 '+shlex.quote(item['home']+'/ha/ha.service')+' /etc/systemd/system/homework-public-source-ha.service\nsudo -n systemctl daemon-reload\nsudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
            else:
                roll.module('application_stop','public-recovery-isolation.py').stop(box)
                save(box/'ha/mac/controller.json',manifest[owner]['controller']);(box/'runtime/STOP').unlink(missing_ok=True)
                subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                    sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)
            paid(owner)
        manifest['application_receipts']=dict(release=revision,protocol=protocol,evidence=str(home),
            candidates={'mac':dict(code=str(NETWORK)),'spark':dict(code=codepath)})
        save(box/'ha/deployment.json',manifest)
        assert roll.spare.rows(before['mac']['service']['database'])==literal
        save(home/'installed.json',dict(release=revision,events=45,head=literal[-1][2],source_admission=before['regeneration']['admission'],
            physical_reboots=0,anchor_restarts=0,stages=progress['stages']))
        print('APPLICATION RECEIPTS INSTALLED: original candidates; original45 and four source views unchanged',flush=True)
    except BaseException:
        for owner,record in frozen.items():
            try:roll.spare.writer_signal(box,before,owner,'SIGCONT',record)
            except Exception:pass
        raise

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);install(p.parse_args().box.resolve())
