"""Inventory registered public roots even when a revoked owner lock lost its monitor."""
import inspect
import ctypes
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


SCHEME = 'registered-public-roots/v1'


def interpreter_aliases(commands):
    paths = set()
    for command in commands:
        paths.add(command[0])
        if len(command) == 6 and command[2] == '--child':
            paths.add(json.loads(command[5])[0])
    aliases = {}
    for path in paths:
        executable = os.path.realpath(shutil.which(path) or path)
        if Path(executable).name.lower().startswith('python'):
            probe = """import ctypes,os,sys
if sys.platform=='darwin':
 b=ctypes.create_string_buffer(4096)
 assert ctypes.CDLL('/usr/lib/libproc.dylib').proc_pidpath(os.getpid(),b,len(b))>0
 print(os.fsdecode(b.value))
else:print(os.readlink('/proc/self/exe'))
"""
            image = subprocess.check_output([path, '-I', '-S', '-c', probe], text=True, timeout=10).strip()
            aliases[executable] = image
    return aliases


def normalized(argv, aliases=None):
    value = list(argv)
    if value:
        value[0] = os.path.realpath(shutil.which(value[0]) or value[0])
        value[0] = (aliases or {}).get(value[0], value[0])
    if len(value) > 1 and value[1] == '-u' and Path(value[0]).name.lower().startswith('python'):
        value.pop(1)
    if len(value) == 6 and value[2] == '--child':
        value[5] = normalized(json.loads(value[5]), aliases)
    return value


def process_argv(pid):
    if sys.platform == 'linux':
        return [os.fsdecode(v) for v in Path('/proc', str(pid), 'cmdline').read_bytes().split(b'\0') if v]
    if sys.platform != 'darwin':
        raise RuntimeError('REGISTERED_ROOT_PLATFORM')
    libc = ctypes.CDLL(None, use_errno=True)
    mib = (ctypes.c_int * 3)(1, 49, pid)
    size = ctypes.c_size_t()
    if libc.sysctl(mib, 3, None, ctypes.byref(size), None, 0):
        raise ProcessLookupError(ctypes.get_errno(), 'procargs size')
    buffer = ctypes.create_string_buffer(size.value)
    if libc.sysctl(mib, 3, buffer, ctypes.byref(size), None, 0):
        raise ProcessLookupError(ctypes.get_errno(), 'procargs')
    data = buffer.raw[:size.value]
    argc = struct.unpack_from('i', data)[0]
    parts = data[4:].split(b'\0')
    index = 1
    while index < len(parts) and not parts[index]:
        index += 1
    return [os.fsdecode(v) for v in parts[index:index+argc]]


def selected(rows, uid, commands, aliases=None):
    if aliases is None:
        aliases = interpreter_aliases(commands)
    expected = [normalized(command, aliases) for command in commands]
    roots = set()
    for row in rows:
        if row['uid'] != uid:
            continue
        try:
            argv = normalized(row['argv'], aliases)
        except (ValueError, TypeError):
            continue
        if argv in expected:
            roots.add(row['pid'])
    owned = set(roots)
    while True:
        children = {r['pid'] for r in rows if r['uid'] == uid and r['parent'] in owned}
        if children <= owned:
            return roots, owned
        owned |= children


def registration(box, manifest, member, network):
    node = manifest['nodes'].get(member)
    commands = []
    if member == 'a':
        code, home = str(network), str(box/'local-anchor')
        owner, state = 'mac', str(box/'runtime')
    else:
        code, home = node['code'], node['home']
        owner = 'spark' if member == 'c' else None
        state = home+'/ha/runtime'
        python = node['python']
        anchor = [python, code+'/live_timing.py', 'anchor', home+'/config.json']
        commands += [[python, code+'/live_timing.py', 'host', home], anchor,
                     [python, code+'/recovery_loop.py', '--child', home+'/state', 'anchor', json.dumps(anchor)]]
    if owner:
        candidate = manifest['application_receipts']['candidates'][owner]['code']
        controller = manifest[owner]['controller']
        service = str(Path(controller['service']).with_name('controller.json'))
        python = controller['members']['a'][0] if member == 'a' else node['python']
        commands.append([python, candidate+'/live_timing.py', 'coordinator', service])
        members = {'ha-member-'+name: argv for name, argv in controller.get('members', {}).items()}
        members['ha-service'] = [python, candidate+'/live_timing.py', 'writer', state+'/ha-service.json']
        for name, argv in members.items():
            commands += [argv, [python, candidate+'/recovery_loop.py', '--child', state, name, json.dumps(argv)]]
    return commands


def query(code, home, source, member, commands, base=None):
    helpers = '\n'.join(inspect.getsource(f) for f in (interpreter_aliases, normalized, process_argv, selected))
    return f'''import ctypes,json,os,shlex,shutil,struct,subprocess,sys,time
from pathlib import Path
sys.path.insert(0,{str(code)!r})
from recovery_loop import birth,boot_identity
from crypto import app_private,sign,digest
{helpers}
rows=[]
for line in subprocess.check_output(['ps','-axo','pid=,ppid=,uid=,command='],text=True).splitlines():
 fields=line.strip().split(None,3)
 if len(fields)==4:
  row=dict(pid=int(fields[0]),parent=int(fields[1]),uid=int(fields[2]),command=fields[3],argv=[])
  if row['uid']==os.getuid():
   try:row['argv']=process_argv(row['pid'])
   except (FileNotFoundError,ProcessLookupError):pass
  rows.append(row)
roots,owned=selected(rows,os.getuid(),{commands!r})
processes=[dict(pid=r['pid'],parent=r['parent'],birth=birth(r['pid']),command=r['command']) for r in rows if r['pid'] in owned]
base={base!r}
if base:
 processes=list({{(p['pid'],p['birth']):p for p in base['body']['processes']+processes}}.values())
body=dict(member={member!r},source={source!r},boot=boot_identity(),processes=processes,
 root_coverage=dict(scheme={SCHEME!r},registration=digest({commands!r}),roots=sorted(roots),base_inventory=base,observed_at=time.time()))
print(json.dumps(sign(app_private(Path({str(home)!r})/'pki/anchor'),'public-epoch-inventory',body)))
'''


def collect(box, manifest, deploy, base=None):
    def node(member):
        code = deploy.NETWORK if member == 'a' else manifest['nodes'][member]['code']
        home = box/'local-anchor' if member == 'a' else manifest['nodes'][member]['home']
        commands = registration(box, manifest, member, deploy.NETWORK)
        script = query(code, home, manifest['source'], member, commands, base[member] if base else None)
        return member, json.loads(deploy.execute(member, script, manifest, 90))
    with ThreadPoolExecutor(max_workers=4) as pool:
        return dict(pool.map(node, 'abcd'))


def bodies(box, manifest, network, records):
    from anchor import public_key
    from crypto import digest, verify
    assert set(records) == set('abcd'), 'DONOR_REGISTERED_ROOT_MEMBERS'
    result = {}
    for member, signed in records.items():
        body = verify(public_key(manifest['trust']['members'][member]), 'public-epoch-inventory', signed)
        assert body['source'] == manifest['source'] and body['member'] == member, 'DONOR_REGISTERED_ROOT_SOURCE'
        coverage = body['root_coverage']
        assert coverage['scheme'] == SCHEME and coverage['registration'] == digest(registration(box, manifest, member, network)), 'DONOR_REGISTERED_ROOT_SCOPE'
        result[member] = body
    return result


def require_empty(box, directory, manifest, deploy):
    import time
    records = collect(box, manifest, deploy)
    values = bodies(box, manifest, deploy.NETWORK, records)
    closed = json.loads((directory/'closed.json').read_text())
    assert all(not v['processes'] and not v['root_coverage']['roots'] for v in values.values()), 'DONOR_REGISTERED_PUBLIC_ROOT_REMAINS'
    assert all(v['boot'] == closed[n]['body']['boot'] for n, v in values.items()), 'DONOR_REGISTERED_ROOT_BOOT'
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    deploy.roll.save(directory/'registered-root-quiescence.json', dict(reports=records, completed_at=time.time(),
        closed=sha(directory/'closed.json'), events=sha(directory/'events.json')))


def private_order(observed, completed, started):
    assert max(observed) <= completed <= started, 'DONOR_REGISTERED_ROOT_PRIVATE_ORDER'


def verify_closed(box, work, manifest, network):
    directory = work/'actual'
    load = lambda p: json.loads(p.read_text())
    batches = load(directory/'raw-inventories.json')
    assert len(batches) == 1, 'DONOR_REGISTERED_ROOT_INVENTORY_REQUIRED'
    before = bodies(box, manifest, network, batches[-1])
    quiescence = load(directory/'registered-root-quiescence.json')
    after = bodies(box, manifest, network, quiescence['reports'])
    closed = load(directory/'closed.json')
    started = load(directory/'private-one-started.json')
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    assert quiescence['closed'] == sha(directory/'closed.json') and quiescence['events'] == sha(directory/'events.json'), 'DONOR_REGISTERED_ROOT_ATTEMPT'
    assert started['binding']['registered_roots'] == sha(directory/'registered-root-quiescence.json'), 'DONOR_REGISTERED_ROOT_PRIVATE_BINDING'
    for member in 'abcd':
        initial, final = before[member], after[member]
        from anchor import public_key
        from crypto import verify
        base = verify(public_key(manifest['trust']['members'][member]), 'public-epoch-inventory', initial['root_coverage']['base_inventory'])
        assert base['member'] == member and base['source'] == manifest['source'] and base['boot'] == initial['boot'], 'DONOR_REGISTERED_ROOT_ORIGINAL_INVENTORY'
        inventory = {(p['pid'], p['birth']): p for p in initial['processes']}
        assert all(inventory.get((p['pid'], p['birth'])) == p for p in base['processes']), 'DONOR_REGISTERED_ROOT_ORIGINAL_TREE'
        assert initial['boot'] == final['boot'] == closed[member]['body']['boot'], 'DONOR_REGISTERED_ROOT_BOOT'
        assert not final['processes'] and not final['root_coverage']['roots'], 'DONOR_REGISTERED_PUBLIC_ROOT_REMAINS'
        assert initial['root_coverage']['observed_at'] <= closed[member]['body']['closed_at'] <= final['root_coverage']['observed_at'], 'DONOR_REGISTERED_ROOT_ORDER'
    private_order([v['root_coverage']['observed_at'] for v in after.values()], quiescence['completed_at'], started['at'])
    return dict(scheme=SCHEME, members=list('abcd'), remaining=0)
