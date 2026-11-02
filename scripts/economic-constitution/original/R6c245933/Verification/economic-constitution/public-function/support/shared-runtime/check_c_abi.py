from pathlib import Path
import hashlib,json,re,shlex,sys
box=Path(__file__).absolute().parent
pattern=re.compile(r'(?m)^(?:(?:LEAN_EXPORT|extern|static) )?(lean_object\*|lean_object\*\*|uint8_t|uint16_t|uint32_t|uint64_t|size_t|double|float) ((?:(?:runtime_|meta_)?initialize_\w+)|run_main|l\w+)\(([^\n()]*)\)\s*[;{]')
if sys.argv[1:]==['--self-test']:
    for name in ['initialize_Test', 'runtime_initialize_Test', 'meta_initialize_Test', 'run_main', 'l_test', 'lp_test']:
        source=f'lean_object* {name}(uint8_t value);\nLEAN_EXPORT lean_object* {name}(lean_object* value) {{'
        signatures={(match[1],match[3]) for match in pattern.finditer(source)}
        assert len(signatures)==2, (name,signatures)
    print('SHARED ABI NEGATIVE CONTROLS PASS: six symbol families reject mismatched argument types, including initializers and run_main')
    raise SystemExit(0)
plan=json.loads((box/'source-plan.json').read_text()); by={r['module']:r for r in plan}
original=json.loads((box.parent/'native/original-project-inputs.json').read_text())
extras={r['moduleName']:r for r in json.loads((box/'extra-exports-plan.json').read_text())}
sources=[box/'generated'/Path(r['module'].replace('.','/')+'.c') if r['module'] in by else Path(extras[r['module']]['path']) if r['module'] in extras else Path(r['c']) for r in original]
sources += [box/'generated'/Path(r['module'].replace('.','/')+'.c') for r in plan if r['module'] not in {p['module'] for p in original}]
assert len(sources)==1148
sources.append(box.parent/'native/NativeBoot.c')
found={};total=0
for path in sources:
    for match in pattern.finditer(path.read_text()):
        params=tuple(re.sub(r'\s+\w+$','',part.strip()) for part in match[3].split(',')) if match[3].strip() not in ['', 'void'] else ()
        signature=repr((match[1],params))
        found.setdefault(match[2],{}).setdefault(signature,[]).append(str(path));total+=1
bad={name:signatures for name,signatures in found.items() if len(signatures)>1}
record=dict(accepted=not bad,c_files=len(sources),declarations=total,symbols=len(found),mismatches=bad,
    input_sha256={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in sources},executable_not_invoked=True)
(box/'c-abi-verification.json').write_text(json.dumps(record,indent=2)+'\n')
assert not bad,('inconsistent C ABI',list(bad)[:12])
print(f'SHARED CROSS-MODULE C ABI PASS: files={len(sources)}; declarations={total}; symbols={len(found)}; mismatches=0; before executable initialization')
