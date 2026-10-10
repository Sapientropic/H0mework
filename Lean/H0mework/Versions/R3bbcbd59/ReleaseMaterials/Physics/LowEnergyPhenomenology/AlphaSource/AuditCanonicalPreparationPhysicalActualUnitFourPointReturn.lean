import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceUnitMixedDerivative
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceUnitAmputatedFourPoint
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceUnitPhysicalCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.PhysicalActualUnitFourPointReturnTypedMouths
import Lean.Elab.Command
import Lean.Util.FoldConsts
open Lean Elab Command
private def usedConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    deps := deps ++ value.getUsedConstants
  match info with
  | .inductInfo value => deps := deps ++ value.ctors.toArray
  | .recInfo value =>
      for rule in value.rules do deps := deps ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return deps

private def completeClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name)))
    (roots : List Name) : IO NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      seen := seen.insert name
      let memo ← cache.get
      let children ← match memo.find? name with
        | some deps => pure deps
        | none => do
          let deps := match env.checked.get.find? name with
            | some info => usedConstants info
            | none => #[]
          cache.modify (fun old => old.insert name deps)
          pure deps
      pending := children.toList ++ pending
  return seen

private def checkClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name))) (roots : List Name) : CommandElabM (Nat × Nat × Nat) := do
  let closure ← liftIO (completeClosure env cache roots)
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut opaqueCount := 0
  let mut axiomCount := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN_NODE {name}"
    if info.isUnsafe then throwError m!"UNSAFE_NODE {name}"
    if info.isPartial then throwError m!"PARTIAL_NODE {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD_VALUE {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axiomCount := axiomCount + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  let forbidden := #[
    `SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
    `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
    `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
    `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed]
  for name in forbidden do
    if closure.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  return (closure.size, opaqueCount, axiomCount)





elab "#audit_physical_actual_unit_four_point_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let aliasOwned := env.constants.toList.filterMap fun (name, _) =>
    if owner name == some `H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.RawActionDensity then some name else none
  unless aliasOwned.isEmpty do throwError m!"NONEMPTY_SOURCE_ONLY_ALIAS {aliasOwned}"
  unless modules.contains `H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRawActionDensity do
    throwError "MISSING_ORIGINAL_CANONICAL_RAW_DENSITY"
  let candidates := #[`H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitMixedDerivative,
    `H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitAmputatedFourPoint,
    `H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitPhysicalCurrent]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitRead,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitRead_original,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitComplexMixed,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitComplexMixed_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex_return,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointForward,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointReverse,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointContact,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointCore,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPoint_factor,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPointPair,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_amputated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_return,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_bound,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeCurrent,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeSlope,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeCurrent_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeParts,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeSlope_parts,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeSlope_bound,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerSlope,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitCoSource_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent_return]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitRead,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitRead_original,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitMixedVertex,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitMixedVertex_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitComplexMixed,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitComplexMixed_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitMixedVertex_return,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceFourPointForward,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceFourPointReverse,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceFourPointContact,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceFourPointCore,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceFourPoint_factor,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitFourPointPair,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitFourPoint_amputated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitFourPoint_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitFourPoint_return,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitFourPoint_bound,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeCurrent,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeSlope,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeCurrent_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeParts,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeSlope_parts,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitTimeSlope_bound,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitEulerCurrent,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitEulerSlope,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitEulerCurrent_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitCoSource_generated,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturnAudit.checked_sourceUnitEulerCurrent_return]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitRead,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitComplexMixed,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointForward,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointReverse,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointContact,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPointCore,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPointPair,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeParts,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent,
    ``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerSlope]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_amputated,``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceFourPoint_factor),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_generated,``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_amputated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent_generated,``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeCurrent_generated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitCoSource_generated,``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeCurrent_generated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex_generated,``LowEnergy.PreparationVacuumJointFieldResponse.mixedVertex_generated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_generated,``LowEnergy.PreparationVacuumJointFieldResponse.mixedVertex_generated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitMixedVertex_return,``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_return),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_return,``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_return),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitFourPoint_amputated,``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_vertex),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeCurrent_generated,``LowEnergy.PreparationVacuumRawJointFeedback.fiveKernel_generated),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeSlope_bound,``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_bound),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitTimeSlope_bound,``LowEnergy.PreparationVacuumPhysicalTailPrice.fiveKernel_price),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent_return,``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_return),
    (``LowEnergy.PreparationPhysicalActualUnitFourPointReturn.sourceUnitEulerCurrent_return,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_original)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_ACTUAL_UNIT_FOUR_POINT_RETURN_OUTPUT") then
    let project := closure.toArray.filter fun name =>
      match owner name with
      | none => false
      | some moduleName => !(#["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph", "ProofWidgets"].any
          (fun head => head.isPrefixOf moduleName.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("engineering_source_only_alias_zero_owned",toJson aliasOwned.isEmpty), ("owned",toJson (owned.map Name.toString)), ("public_roots",toJson mouths.size),
      ("nodes",toJson nodes), ("opaque_all_read",toJson opaques), ("axioms",toJson axioms),
      ("anchors",toJson (anchors.map Name.toString)),
      ("consumers",toJson (consumers.map fun p => (p.1.toString,p.2.toString))),
      ("actual_tests",toJson (tests.map Name.toString)),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"ACTUAL_UNIT_FOUR_POINT_RETURN_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_physical_actual_unit_four_point_return
