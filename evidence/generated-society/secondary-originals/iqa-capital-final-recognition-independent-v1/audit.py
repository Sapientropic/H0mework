#!/usr/bin/env python3
import hashlib,json,os,subprocess,time
from pathlib import Path
ROOT=Path('.')
LEAN=ROOT/'Lean'
OUT=Path(__file__).resolve().parent
CAPSULE=OUT/'audit-input.json'
data=json.loads(CAPSULE.read_text())
LIB=OUT/'lib'
modules={Path(row['relative_path']).with_suffix('').as_posix().replace('/','.'):row for row in data['owned_files']}
checks=json.loads((OUT/'checks.json').read_text())
selected=data['closure']
owned_paths={row['relative_path'] for row in data['owned_files']}
order=list(modules)
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def source_check():
 for relative,row in data['closure'].items():
  if digest(Path(row.get('source_path',str(LEAN/relative))))!=row['source_sha256']:raise RuntimeError('changed source during final audit '+relative)
source_check()
selected_start={}
for relative in selected:
 artifact=LIB/Path(relative).with_suffix('.olean')
 selected_start[relative]={suffix or '.olean':digest(Path(str(artifact)+suffix)) for suffix in ['', '.private', '.server'] if Path(str(artifact)+suffix).exists()}
(OUT/'selected-start.json').write_text(json.dumps(selected_start,indent=2)+'\n')
lake_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=LEAN,text=True).strip()
compiler=subprocess.check_output(['lake','env','which','lean'],cwd=LEAN,text=True).strip()
env=dict(os.environ,LEAN_PATH=str(LIB)+':'+lake_path)
def run_check(name,source,artifact=None):
 cmd=[compiler,'--trust=0','-j1','-M12000','-DElab.async=false','-DwarningAsError=true']
 if artifact:cmd += ['-o',str(artifact)]
 cmd.append(str(source))
 log=OUT/(name+'.log');started=time.monotonic()
 with log.open('w') as stream:
  result=subprocess.run(cmd,cwd=LEAN,env=env,stdout=stream,stderr=subprocess.STDOUT)
 row={'name':name,'source':str(source),'source_sha256':digest(source),'exit':result.returncode,'seconds':round(time.monotonic()-started,3),'command':cmd,'log':str(log)}
 checks.append(row);(OUT/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
 print(('PASS ' if result.returncode==0 else 'FAIL ')+name+' '+str(row['seconds'])+'s',flush=True)
 if result.returncode:
  print(log.read_text()[-20000:],flush=True)
  raise RuntimeError('audit gate failed '+name)
 return log.read_text()
imports = '\n'.join('import ' + module for module in modules)
inventory_source = OUT / 'public-inventory.lean'
inventory_source.write_text(imports + '\nimport Lean.Elab.Command\nopen Lean Elab Command\n' + r'''
elab "#priority_public_inventory" : command => do
  let env ← getEnv
  let owned := #[MODULES]
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains) &&
        !info.isUnsafe && !info.isPartial && (privateToUserName? name).isNone then some name.toString else none
  liftIO <| IO.FS.writeFile "NAME_PATH" (String.intercalate "\n" (names.mergeSort (· ≤ ·)))
#priority_public_inventory
'''.replace('MODULES', ','.join('`' + module for module in modules)).replace('NAME_PATH',str(OUT / 'fresh-public-names.txt')))
run_check('public-inventory', inventory_source)
data['explicit_public_declarations'] = []
data['public_declarations'] = [{'name':name} for name in (OUT / 'fresh-public-names.txt').read_text().splitlines() if name]
(OUT / 'final-public-inventory.json').write_text(json.dumps(data['public_declarations'],indent=2)+'\n')
axioms = OUT / 'public-axioms.lean'
axioms.write_text(imports + '\n\nset_option linter.auxLemma false\n' + '\n'.join('#print axioms ' + row['name'] for row in data['public_declarations']) + '\n')
axiom_log = run_check('public-axioms', axioms)

kernel_template = r'''
import Lean.Replay
import Lean.Elab.Command
import Lean.Util.FoldConsts
open Lean Elab Command
set_option maxRecDepth 100000

private partial def collect (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then collect env rest seen
    else match env.find? name with
      | none => collect env rest (seen.insert name)
      | some info => collect env (info.getUsedConstantsAsSet.toList ++ rest) (seen.insert name)

elab "#check_final_recognition_kernel" : command => do
  let env ← getEnv
  let owned := #[OWNED_MODULES]
  let ownedEntries := env.constants.toList.filter fun (name, _) =>
    ((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains
  let roots := ownedEntries.filterMap fun (name, info) =>
    if !info.isUnsafe && !info.isPartial then some name else none
  let excluded := ownedEntries.filterMap fun (name, info) =>
    if info.isUnsafe || info.isPartial then some name else none
  liftIO <| IO.FS.writeFile "runtime/audit-tmp/iqa-capital-final-recognition-independent-v1/excluded-ir.txt" (String.intercalate "\n" (excluded.map Name.toString))
  if roots.isEmpty then throwError "empty FinalRecognition audit"
  let closure := collect env roots
  let mut inventory : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut privateCount := 0
  for name in closure do
    let some info := env.find? name | throwError "missing dependency {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe or partial logical dependency {name}"
    inventory := inventory.insert name info
    if (privateToUserName? name).isSome then privateCount := privateCount + 1
    if info matches .axiomInfo _ then axioms := axioms.push name
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "unauthorized axiom {axiomName}"
  liftIO <| IO.FS.writeFile "INVENTORY_PATH" (String.intercalate "\n" ((inventory.toList.map fun (name, _) => name.toString).mergeSort (· ≤ ·)))
  logInfo m!"KERNEL REPLAY START: roots={roots.length}, closure={inventory.size}, private={privateCount}, excludedIR={excluded.length}, axioms={axioms}"
  let fresh ← liftIO (mkEmptyEnvironment 0)
  let _ ← liftIO (Environment.replay inventory fresh)
  logInfo m!"KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, excludedIR={excluded.length}, axioms={axioms}"

#check_final_recognition_kernel
'''
kernel_template = kernel_template.replace('OWNED_MODULES', ',\n    '.join('`' + m for m in list(modules) + data.get('support_kernel_modules', [])))
kernel_template = kernel_template.replace('INVENTORY_PATH', str(OUT / 'kernel-inventory.txt'))
kernel_source = OUT / 'kernel-replay.lean'
kernel_source.write_text(imports + '\n' + kernel_template)
kernel_log = run_check('kernel-replay', kernel_source)
if 'KERNEL REPLAY PASS:' not in kernel_log:
    raise RuntimeError('missing current-environment replay verdict')

source_check()
for relative,row in selected.items():
 artifact=LIB/Path(relative).with_suffix('.olean')
 if not artifact.exists():raise RuntimeError('missing selected '+relative)
 for suffix,expected in selected_start[relative].items():
  path=artifact if suffix=='.olean' else Path(str(artifact)+suffix)
  if digest(path)!=expected:raise RuntimeError('selected artifact changed during audit '+relative+suffix)
 row['selected_olean']=str(artifact)
 row['selected_olean_sha256']=digest(artifact)
 row['selected_siblings']={}
 for suffix in ['', '.private', '.server']:
  path=Path(str(artifact)+suffix)
  if path.exists():row['selected_siblings'][suffix or '.olean']={'path':str(path),'sha256':digest(path)}
(OUT/'selected-imports.json').write_text(json.dumps(selected,indent=2)+'\n')
receipt={'schema':'capital-final_recognition-independent-certify/v1','phase':'certify','status':'T1','capsule':str(CAPSULE),'capsule_sha256':digest(CAPSULE),'compiler':compiler,'compiler_version':subprocess.check_output([compiler,'--version'],text=True).strip(),'source_modules':len(selected),'owned_modules':len(order),'new_independent_focused_modules':len(order),'reused_previous_independent_focused_modules':0,'public_mouths':len(data['public_declarations']),'checks':checks,'public_axioms':axiom_log,'kernel':kernel_log.strip()}
(OUT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('T1 receipt '+str(OUT/'verification.json'),flush=True)
