"""Read the original sealed Lean source independently before accepting an event."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import time

from crypto import digest
from recovery_loop import birth, boot_identity


class Incomplete(ValueError):
    def __init__(self, reason):
        self.reason = reason
        super().__init__('SEMANTIC_INCOMPLETE')


class Mismatch(ValueError):
    def __init__(self, witness):
        self.witness = witness
        super().__init__('SEMANTIC_VIOLATION')


class Engine:
    def __init__(self, config):
        self.config = config; self.process = None; self.error = None; self.buffer = b''
        self.count = 0; self.head = '0'*64
        self.descriptor = config['descriptor']
        try:self.validate()
        except Incomplete:raise
        except (OSError,ValueError,KeyError,TypeError) as problem:
            raise Incomplete('SOURCE_CONFIGURATION') from problem

    def validate(self):
        config=self.config
        exporter = Path(config['exporter'])
        expected=self.descriptor['exporter_sha256']
        specialization=config.get('private_exporter')
        if specialization is not None:
            if (set(specialization)!={'original_exporter_sha256','exporter_sha256','contract','contract_sha256'} or
                    specialization['original_exporter_sha256']!=expected or
                    hashlib.sha256(Path(specialization['contract']).read_bytes()).hexdigest()!=specialization['contract_sha256']):
                raise Incomplete('PRIVATE_EXPORTER_BINDING')
            expected=specialization['exporter_sha256']
        if hashlib.sha256(exporter.read_bytes()).hexdigest() != expected:
            raise Incomplete('EXPORTER_CHANGED')
        closure = Path(config['closure'])
        if hashlib.sha256(closure.read_bytes()).hexdigest() != self.descriptor['closure_sha256']:
            raise Incomplete('CLOSURE_CHANGED')
        inventory = json.loads(closure.read_text())
        for name, wanted in inventory.items():
            path = Path(config['lean_path'])/name
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != wanted:
                raise Incomplete('SOURCE_ARTIFACT_CHANGED')
        variant=config.get('private_variant','private-one')
        if (variant not in {'private-one','private-two'} or len(config['backend'])!=6 or
                config['backend'][1:4]!=['--trust=0','-j1','--run'] or
                Path(config['backend'][4]).resolve()!=exporter.resolve() or config['backend'][5]!=variant):
            raise Incomplete('CANONICAL_SOURCE_REQUIRED')
        try:
            compiler=subprocess.check_output([config['backend'][0],'--githash'],text=True,timeout=5).strip()
        except (OSError,subprocess.SubprocessError) as problem:
            raise Incomplete('COMPILER_UNAVAILABLE') from problem
        if compiler!=self.descriptor['compiler']:raise Incomplete('COMPILER_CHANGED')

    def close(self):
        if self.process:
            if self.process.poll() is None:
                self.process.stdin.close()
                try:self.process.wait(timeout=.2)
                except subprocess.TimeoutExpired:
                    try:os.killpg(self.process.pid, signal.SIGTERM)
                    except ProcessLookupError:pass
                    except PermissionError:self.process.terminate()
                    try:self.process.wait(timeout=.2)
                    except subprocess.TimeoutExpired:
                        try:os.killpg(self.process.pid, signal.SIGKILL)
                        except ProcessLookupError:pass
                        except PermissionError:self.process.kill()
                        self.process.wait(timeout=2)
            self.process.stdin.close();self.process.stdout.close();self.process = None
        if self.error:self.error.close();self.error = None
        self.count = 0; self.head = '0'*64; self.buffer = b''

    def start(self):
        self.close()
        env = os.environ.copy();env['LEAN_PATH'] = self.config['lean_path']
        try:
            self.error = Path(self.config['error_log']).open('ab')
            self.process = subprocess.Popen(self.config['backend'], cwd=self.config['cwd'],env=env,
                stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.error,start_new_session=True,bufsize=0)
        except OSError as problem:
            self.close();raise Incomplete('SOURCE_START') from problem

    def call(self, body, deadline):
        try:
            if self.process is None or self.process.poll() is not None:
                raise Incomplete('SOURCE_WORKER_EXITED')
            self.process.stdin.write((json.dumps(body)+'\n').encode());self.process.stdin.flush()
            with selectors.DefaultSelector() as selector:
                selector.register(self.process.stdout, selectors.EVENT_READ)
                while b'\n' not in self.buffer:
                    if not selector.select(max(0,deadline-time.monotonic())):
                        raise Incomplete('SOURCE_TIMEOUT')
                    chunk = os.read(self.process.stdout.fileno(),65536)
                    if not chunk:raise Incomplete('SOURCE_EOF')
                    self.buffer += chunk
                    if len(self.buffer)>65536:raise Incomplete('SOURCE_FRAME')
            line,self.buffer = self.buffer.split(b'\n',1);result = json.loads(line)
            if 'error' in result:raise Incomplete('SOURCE_REJECTED_INPUT')
            return result
        except Incomplete:
            self.close();raise
        except (OSError,ValueError,TypeError) as problem:
            self.close();raise Incomplete(type(problem).__name__) from problem

    def sync(self, rows, deadline=None):
        if (self.process is None or self.process.poll() is not None or self.count>len(rows) or
                self.count and rows[self.count-1][2]!=self.head):
            self.start()
        deadline=deadline if deadline is not None else time.monotonic()+self.config.get('replay_seconds',20)
        try:
            for seq,previous,head,text in rows[self.count:]:
                if seq!=self.count+1 or previous!=self.head:raise Incomplete('PREFIX_CHAIN')
                event=json.loads(text)['body']
                from source_extension import guard
                guard(self.config.get('governance_context', {}), rows[:self.count], event)
                from governance import registration_bound
                registration_bound(event)
                if event['type']=='disclosure':
                    state=self.call({'op':'inspect'},deadline);record=event['record']
                    if state['cut']!=record['cut']:raise Incomplete('PREFIX_SOURCE_CUT')
                    actual=self.call({'op':'advance','cut':state['cut'],'query':record['query']},deadline)
                    if actual!=record:raise Incomplete('PREFIX_SOURCE_RECORD')
                elif event['type']=='native-response':
                    from governance import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type'] in {'energy-renewal','energy-audit'}:
                    from energy import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-continuation':
                    from continuation import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-handoff':
                    from handoff import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='source-extension':
                    from source_extension import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='material-extension':
                    from material_extension import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type'] in {'donor-extension','energy-donor'}:
                    from donor_arrival_live import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='arrival-extension':
                    from arrival_extension import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-arrival':
                    from arrival_regeneration import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='productive-extension':
                    from productive_extension import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-productive':
                    from productive_regeneration import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-material':
                    from material_regeneration import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']=='energy-regeneration':
                    from regeneration import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                elif event['type']!='rotation':raise Incomplete('PREFIX_EVENT_KIND')
                if 'registration' in event:
                    from governance import expected
                    expected(self.config['governance_context'],rows[:self.count],event)
                self.count=seq;self.head=head
        except (Incomplete,ValueError,KeyError,TypeError) as problem:
            # A failed prefix may already have advanced the private worker.
            # Discard it before retrying the committed journal from the start.
            self.close()
            if isinstance(problem,Incomplete):raise
            raise Incomplete('PREFIX_DATA') from problem

    def check(self, rows, message):
        self.sync(rows);event=message['body']
        from source_extension import guard
        guard(self.config.get('governance_context', {}),rows,event)
        from governance import registration_bound
        registration_bound(event)
        from supply_disposition import FEATURES, compare
        if event['type'] in FEATURES:
            return compare(self, rows, message)
        if event['type']=='rotation':return None
        if event['type'] in {'energy-renewal','energy-audit'}:
            from energy import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-continuation':
            from continuation import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-handoff':
            from handoff import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='source-extension':
            from source_extension import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='material-extension':
            from material_extension import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type'] in {'donor-extension','energy-donor'}:
            from donor_arrival_live import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='arrival-extension':
            from arrival_extension import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-arrival':
            from arrival_regeneration import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='productive-extension':
            from productive_extension import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-productive':
            from productive_regeneration import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-material':
            from material_regeneration import expected
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']=='energy-regeneration':
            from regeneration import expected
            expected(self.config['governance_context'],rows,event)
            return None
        from governance import expected,response_at
        if event['type']=='native-response':
            expected(self.config['governance_context'],rows,event)
            return None
        if event['type']!='disclosure' or event['request']['kind']!='audit':
            raise Incomplete('SOURCE_EVENT_KIND')
        if response_at(rows):raise Incomplete('NATIVE_NEW_SCOPE_REQUIRED')
        body=event['request']['body'];deadline=time.monotonic()+self.config.get('step_seconds',2)
        state=self.call({'op':'inspect'},deadline)
        if any(state[k]!=body[field] for k,field in [('cut','cut'),('version','epoch')]) or state['actor']!=int(body['actor']):
            raise Incomplete('REQUEST_NOT_CURRENT_SOURCE_INPUT')
        expected=self.call({'op':'preview','cut':state['cut'],'query':body['query']},deadline)
        witness={'classification':'verified','source':event['source'],'stream':event['stream'],
                 'prefix':{'seq':self.count,'head':self.head},'event':digest(message),
                 'expected':expected,'actual':event['record'],'descriptor':self.descriptor}
        if expected!=event['record']:
            witness['classification']='invalid';raise Mismatch(witness)
        if 'registration' in event:
            from governance import expected as native_expected
            native_expected(self.config['governance_context'],rows,event)
        return witness

    def status(self):
        process=self.process
        return {'prefix':{'seq':self.count,'head':self.head},'descriptor':self.descriptor,
                'backend':{'pid':process.pid,'birth':birth(process.pid),'pgid':os.getpgid(process.pid),'boot':boot_identity()}
                    if process and process.poll() is None else None}
