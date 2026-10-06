from pathlib import Path
import json
r=Path.cwd(); c=r/'.cache/fixed-mother-promotion'; m=json.loads((c/'manifest.json').read_text()); pairs=[(i['candidate_module'],i['production_module']) for i in m['files']]
old=(r/'.cache/cumulative-admitted-world-promotion/MetadataParity.lean').read_text()
header='\n'.join('import '+b for a,b in pairs)+'\nimport Lean\n\nopen Lean Elab Command\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n'
names='private def moduleRelocations : NameMap Name :=\n  '+''.join('(' for _ in pairs)+'({} : NameMap Name)'+''.join('.insert `'+a+' `'+b+')' for a,b in pairs)+'\n'
names+='private def privateRelocations : NameMap Name :=\n  '+''.join('(' for _ in pairs)+'({} : NameMap Name)'+''.join('.insert `_private.'+a+' `_private.'+b+')' for a,b in pairs)+'\n'
names+=old[old.index('private def binderModulePrefix'):old.index('private def relocatedAuxPart')]
names+='''private partial def productionName (name : Name) : Name :=
  if let some renamed := moduleRelocations.find? name then renamed
  else if let some renamed := privateRelocations.find? name then renamed
  else if let some renamed := binderModulePrefix name then productionName renamed
  else match name with
    | .anonymous => .anonymous
    | .str parent text => .str (productionName parent) text
    | .num parent number => .num (productionName parent) number
private def relocatedModule (name : Name) : Name := (moduleRelocations.find? name).getD name
private def sourceEdits : Option Name → List (Nat × Nat × Nat)
'''
for i in m['files']: names+='  | some `'+i['candidate_module']+' => ['+', '.join('('+', '.join(map(str,e))+')' for e in i['edits'])+']\n'
names+='  | _ => []\n'
helpers=old[old.index('private def sourcePositionMatches'):old.index('run_cmd do')]
body='''run_cmd do
  let production ← getEnv
  Lean.enableInitializersExecution
  let candidate ← importModules CANDIDATE_IMPORTS {} 0 (loadExts := true)
  let candidateModules := CANDIDATE_MODULES
  let productionModules := PRODUCTION_MODULES
  let owner := fun (env : Environment) name =>
    (env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i.toNat]!)
  let (own, codegen) ← match moduleInventory candidate candidateModules with
    | .ok value => pure value
    | .error message => throwError message
  let (after, afterCodegen) ← match moduleInventory production productionModules with
    | .ok value => pure value
    | .error message => throwError message
  let mappedOwn := own.toArray.foldl (fun result name => result.insert (productionName name)) ({} : NameSet)
  unless own.size == 64 && mappedOwn.size == own.size && mappedOwn.size == after.size &&
      after.toArray.all mappedOwn.contains do throwError "OWN_INVENTORY_BIJECTION {own.size} {after.size}"
  unless codegen.isEmpty && afterCodegen.isEmpty do throwError "UNEXPECTED_CODEGEN"
  for module in production.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
  let firstInstances := (Meta.instanceExtension.getState candidate).instanceNames
  let lastInstances := (Meta.instanceExtension.getState production).instanceNames
  for name in own.toArray do
    let moved := productionName name
    let some first := candidate.checked.get.find? name | throwError "OWN_MISSING {name}"
    let some last := production.checked.get.find? moved | throwError "PRODUCTION_MISSING {moved}"
    let sameExpr := completeExprEqual productionName (relocatedMetadata (sourceEdits (owner candidate name))) true
    unless (owner candidate name).map relocatedModule == owner production moved do throwError "OWN_OWNER {name}"
    unless sameLevelParameters productionName first.levelParams last.levelParams do throwError "OWN_LEVEL_PARAMETERS {name}"
    unless sameExpr first.type last.type do throwError "OWN_TYPE {name}: {explainExpr productionName (relocatedMetadata (sourceEdits (owner candidate name))) first.type last.type}"
    unless (match first.value? true, last.value? true with
      | some a, some b => sameExpr a b
      | none, none => true
      | _, _ => false) do throwError "OWN_VALUE {name}: {match first.value? true, last.value? true with | some a, some b => explainExpr productionName (relocatedMetadata (sourceEdits (owner candidate name))) a b | _, _ => "missing"}"
    unless sameDeclarationMetadata productionName sameExpr first last do throwError "OWN_METADATA {name}"
    unless firstInstances.contains name == lastInstances.contains moved do throwError "INSTANCE_CHANGED {name}"
  let full := promotionClosure candidate own.toArray.toList
  let productionFull := promotionClosure production after.toArray.toList
  let mappedFull := full.toArray.foldl (fun result name => result.insert (productionName name)) ({} : NameSet)
  unless mappedFull.size == full.size && full.size == productionFull.size &&
    productionFull.toArray.all mappedFull.contains do throwError "CLOSURE_BIJECTION"
  let mut edges := 0
  let mut shared : Nat := 0
  let mut sharedOwners : NameSet := {}
  let mut axioms : NameSet := {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in full.toArray do
    let moved := productionName name
    let some first := candidate.checked.get.find? name | throwError "UNCHECKED_CANDIDATE {name}"
    let some last := production.checked.get.find? moved | throwError "UNCHECKED_PRODUCTION {moved}"
    unless (owner candidate name).map relocatedModule == owner production moved do throwError "CLOSURE_OWNER {name}"
    if first.isUnsafe || first.isPartial || last.isUnsafe || last.isPartial then throwError "UNSAFE_PARTIAL {name}"
    let beforeRefs := completeRefs first
    let afterRefs := completeRefs last
    let mappedRefs := beforeRefs.toArray.foldl (fun result ref => result.insert (productionName ref)) ({} : NameSet)
    unless mappedRefs.size == beforeRefs.size && beforeRefs.size == afterRefs.size &&
      afterRefs.toArray.all mappedRefs.contains do throwError "CLOSURE_EDGE_BIJECTION {name}"
    edges := edges + beforeRefs.size
    if !own.contains name then
      unless moved == name && owner candidate name == owner production name do throwError "SHARED_MODULE_CHANGED {name}"
      shared := shared + 1
      if let some module := owner candidate name then sharedOwners := sharedOwners.insert module
    match first, last with
    | .axiomInfo _, .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAUTHORIZED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _, .defnInfo _ | .thmInfo _, .thmInfo _ | .opaqueInfo _, .opaqueInfo _ =>
        unless (first.value? true).isSome && (last.value? true).isSome do throwError "MISSING_VALUE {name}"
    | _, _ => pure ()
  let sampleName := `fixedMotherAuditUniverse
  let sampleLevel := Level.param sampleName
  let same := completeExprEqual productionName exactMetadata true
  unless same (.sort sampleLevel) (.sort sampleLevel) do throwError "LEVEL_POSITIVE_CONTROL"
  if same (.sort (.succ sampleLevel)) (.sort sampleLevel) ||
      same (.const ``Nat [.succ sampleLevel]) (.const ``Nat [sampleLevel]) then
    throwError "UNIVERSE_STRUCTURE_COLLAPSED"
  IO.FS.writeFile ".cache/fixed-mother-promotion/shared-owner-modules.json" (toJson (sharedOwners.toArray.map Name.toString)).pretty
  IO.FS.writeFile ".cache/fixed-mother-promotion/parity-own-names.json" (toJson (after.toArray.map Name.toString)).pretty
  logInfo m!"FIXED_MOTHER_PARITY own={own.size} complete_type_value_metadata=1 full_closure={full.size} full_edges={edges} shared_same_module_olean_nodes={shared} owner_edge_bijection=1 axioms={axioms.toArray} unsafe=0 partial=0 codegen=0 instance_delta=0 universe_structure_negative_controls=1"
'''
body=body.replace('CANDIDATE_IMPORTS','#['+', '.join('{module := `'+a+'}' for a,b in pairs)+']').replace('CANDIDATE_MODULES','#['+', '.join('`'+a for a,b in pairs)+']').replace('PRODUCTION_MODULES','#['+', '.join('`'+b for a,b in pairs)+']')
(c/'Parity.lean').write_text(header+names+helpers+body)
print('PARITY_PREPARED',len((header+names+helpers+body).splitlines()),'lines')
