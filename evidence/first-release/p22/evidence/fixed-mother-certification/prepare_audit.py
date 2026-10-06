from pathlib import Path
r=Path.cwd(); c=r/'.cache/fixed-mother-certification'
old=(r/'docs/audits/physics/source-uniqueness/MotherCumulativeAdmittedWorld.lean').read_text()
helpers=old[old.index('private def completeRefs'):old.index('run_cmd do')]
header='import scratch.MotherSourceTheorem.Formation\nimport scratch.MotherSourceTheorem.CompleteRealization\nimport Lean\n\nopen Lean Elab Command\nopen SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness\nopen FixedMotherRealization\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n'
body='''run_cmd do
  let env ← getEnv
  let modules := #[`scratch.MotherSourceTheorem.Formation, `scratch.MotherSourceTheorem.CompleteRealization]
  let own ← match moduleNames env modules with
    | .ok names => pure names
    | .error message => throwError message
  let closure := recoveryClosure env own.toArray.toList
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAUTHORIZED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_VALUE {name}"
    | _ => pure ()
  let mouth := ``root_admission_fixed_mother_complete_realization
  let some info := env.checked.get.find? mouth | throwError "MISSING_MOUTH"
  unless recoveryArity info.type == 0 do throwError "PUBLIC_PREMISE"
  let roots := recoveryClosure env [mouth]
  for required in [``low_formation, ``high_formation, ``MotherAdmittedWorld.every_state,
      ``MotherCompleteInquiry.every_source, ``MotherMacroSource.every_source,
      ``MotherFamilyOccurrence.MotherRoot, ``MotherFamilyOccurrence.MotherVisit,
      ``MotherPointwiseLaws.finiteLaw, ``MotherAdmittedWorld.formState,
      ``MotherMacroSource.Origin.form, ``MotherMaterialJoin.Mixed.combine] do
    unless roots.contains required do throwError "PROVENANCE_MISSING {required}"
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString && !modules.contains module then
      throwError "UNEXPECTED_SCRATCH {module}"
  for name in [``lowProgramme_read, ``highProgramme_read, ``low_formation, ``high_formation, mouth] do
    let some info := env.checked.get.find? name | throwError "MOUTH_MISSING {name}"
    let used ← collectAxioms name
    logInfo m!"MOUTH {name} arity={recoveryArity info.type} levels={info.levelParams} type={info.type} axioms={used}"
  let registered := (Meta.instanceExtension.getState env).instanceNames
  let instances := own.toArray.filter registered.contains
  let mut codegen : Nat := 0
  for module in modules do
    let some index := env.getModuleIdx? module | throwError "MISSING_MODULE"
    let data := env.header.moduleData[index.toNat]!
    for name in data.extraConstNames do
      if !(env.checked.get.find? name).isSome then
        unless data.constNames.any (fun base => base.isPrefixOf name) do throwError "CODEGEN_ORIGIN {name}"
        unless !closure.contains name do throwError "TRUSTED_CODEGEN {name}"
        codegen := codegen + 1
  IO.FS.writeFile ".cache/fixed-mother-certification/own-names.json" (toJson (own.toArray.map Name.toString)).pretty
  IO.FS.writeFile ".cache/fixed-mother-certification/closure-names.json" (toJson (closure.toArray.map Name.toString)).pretty
  logInfo m!"FIXED_MOTHER_TRUST own={own.size} closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0 instances={instances.size} codegen_only={codegen} mouth_arity=0 full_metadata=1"
'''
(c/'Audit.lean').write_text(header+helpers+body)
