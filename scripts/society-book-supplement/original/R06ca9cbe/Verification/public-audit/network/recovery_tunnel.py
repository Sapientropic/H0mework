"""Resolve the current guarded WSL address before each owned SSH tunnel start."""
import argparse
import base64
import hashlib
import ipaddress
import json
import os
from pathlib import Path
import sys
import subprocess
import time

from recovery_loop import boot_identity, save


def ensure_lifetime(node, home):
    from pathlib import PurePosixPath
    path=PurePosixPath(home)
    if '..' in path.parts or not home.startswith(node.c.remote_home+'/workloads/'):
        raise ValueError('WSL_LIFETIME_WORKLOAD')
    source=Path(__file__).with_name('wsl_lifetime.py').read_bytes()
    code=f'''import base64,hashlib,json,time
from pathlib import Path
p=Path({home!r});assert (p/'config.json').is_file()
script=p/'wsl-lifetime.py';raw=base64.b64decode({base64.b64encode(source).decode()!r})
if not script.exists() or hashlib.sha256(script.read_bytes()).hexdigest()!={hashlib.sha256(source).hexdigest()!r}:script.write_bytes(raw)
receipt=p/'wsl-lifetime.json';v=json.loads(receipt.read_text()) if receipt.exists() else {{}}
print(json.dumps(bool(v and v['boot']==Path('/proc/sys/kernel/random/boot_id').read_text().strip() and time.time()-v['at']<15)))
'''
    alive=json.loads(node.wsl("python3 - <<'LIFETIME'\n"+code+"\nLIFETIME\n",20,allow_probe=False))
    if alive:return
    command=subprocess.list2cmdline(['wsl.exe','-d',node.c.distro,'-u',node.c.wsl_user,
                                    '--','/usr/bin/python3',home+'/wsl-lifetime.py',home])
    script="$cmd = '"+command.replace("'","''")+"'\n"
    script+="$r = Invoke-CimMethod -ClassName Win32_Process -MethodName Create -Arguments @{CommandLine=$cmd}\n\"$($r.ReturnValue) $($r.ProcessId)\"\n"
    result=node._run_remote([*node.ssh,'powershell','-NoProfile','-Command','-'],
                            input=script.encode(),capture_output=True,timeout=30,allow_probe=False)
    if result.returncode or not result.stdout.decode().strip().startswith('0 '):
        raise RuntimeError('WSL_LIFETIME_START_FAILED')


def destination(node):
    raw = node.wsl("ip -json route get 1.1.1.1\n", 20, allow_probe=False)
    address = json.loads(raw)[0]['prefsrc']
    ipaddress.IPv4Address(address)
    return address


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--local-port', type=int, required=True)
    parser.add_argument('--remote-port', type=int, required=True)
    parser.add_argument('--lifetime-home')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(root/'ComputeNode/mac'))
    from pcnode import Config, Node
    cfg = Config.load(args.config); node = Node(cfg, args.state)
    if cfg.native:
        raise ValueError('DYNAMIC_WSL_TUNNEL_REQUIRES_WSL_NODE')
    if args.lifetime_home:ensure_lifetime(node,args.lifetime_home)
    for port in (args.local_port, args.remote_port):
        if not 1 <= port <= 65535:
            raise ValueError('TUNNEL_PORT')
    # Node.wsl participates in the shared transport gate. This lookup does not
    # contact the Internet; the kernel only reads its current routing table.
    address = destination(node)
    command = [*node.ssh[:-1], '-N', '-o', 'ControlMaster=no', '-o', 'ControlPath=none',
               '-o', 'ForkAfterAuthentication=no', '-o', 'ExitOnForwardFailure=yes', '-L',
               f'127.0.0.1:{args.local_port}:{address}:{args.remote_port}', cfg.remote]
    save(args.runtime/'wsl-tunnel-resolution.json', {'address': address, 'at': time.time(),
         'boot': boot_identity(), 'command': command, 'owner_monitor': os.getppid()})
    os.execvp(command[0], command)


if __name__ == '__main__':
    main()
