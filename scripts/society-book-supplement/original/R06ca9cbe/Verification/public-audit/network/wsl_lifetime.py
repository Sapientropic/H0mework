"""Keep this workload's WSL client alive outside the transient SSH job."""
import fcntl
import json
import os
from pathlib import Path
import signal
import sys
import time

home=Path(sys.argv[1])
lock=(home/'wsl-lifetime.lock').open('a')
try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
except BlockingIOError:raise SystemExit(0)
signal.signal(signal.SIGTERM,lambda *_:(_ for _ in ()).throw(SystemExit(0)))
while not (home/'WSL-LIFETIME-STOP').exists():
    value={'pid':os.getpid(),'boot':Path('/proc/sys/kernel/random/boot_id').read_text().strip(),'at':time.time(),
           'workload':str(home),'stop':'WSL-LIFETIME-STOP'}
    temp=home/'wsl-lifetime.json.tmp';temp.write_text(json.dumps(value)+'\n');temp.replace(home/'wsl-lifetime.json')
    time.sleep(5)
