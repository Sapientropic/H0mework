"""Exercise actual timeout, partial-line and malformed-output retirement."""
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
from privacy_transport import Worker


def check():
    results=[]
    cases=[('timeout',"import sys,time;sys.stdin.readline();time.sleep(2);print('{}',flush=True)", 'PUBLIC_WORKER_TIMEOUT'),
           ('partial',"import sys,time;sys.stdin.readline();sys.stdout.write('{');sys.stdout.flush();time.sleep(2)", 'PUBLIC_WORKER_TIMEOUT'),
           ('bad-json',"import sys;sys.stdin.readline();print('bad',flush=True);sys.stdin.readline();print('{}',flush=True)", 'PUBLIC_WORKER_ENCODING')]
    for name,code,expected in cases:
        with tempfile.TemporaryDirectory(prefix='privacy-worker-')as temporary:
            worker=object.__new__(Worker)
            worker.errors=(Path(temporary)/'errors').open('w')
            worker.process=subprocess.Popen([sys.executable,'-c',code],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=worker.errors,bufsize=0)
            worker.lock=threading.RLock();worker.poisoned=False;worker.timeout=.1
            try:
                try:worker.call({'request':'first'})
                except RuntimeError as error:assert str(error)==expected,(name,str(error))
                else:raise AssertionError('FIRST_ACCEPTED '+name)
                assert worker.process.poll()is not None and worker.poisoned
                try:worker.call({'request':'next'})
                except RuntimeError as error:assert str(error)=='PUBLIC_WORKER_RECOVERY_REQUIRED'
                else:raise AssertionError('STALE_ANSWER_ACCEPTED '+name)
                results.append(name)
            finally:worker.close()
    return results


if __name__=='__main__':print('WORKER RETIREMENT PASS:',', '.join(check()),'; no stale output accepted by next request')
