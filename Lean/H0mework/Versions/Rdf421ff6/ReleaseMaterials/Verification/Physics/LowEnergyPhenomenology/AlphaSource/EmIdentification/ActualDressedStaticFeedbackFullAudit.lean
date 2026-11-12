import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticFeedback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticCurrentCircuit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticLongrangeReturn

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit
elab "checked_actual_static_rayContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray).type
theorem checked_actual_static_ray : checked_actual_static_rayContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray

elab "checked_actual_corrected_static_feedbackContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback).type
theorem checked_actual_corrected_static_feedback : checked_actual_corrected_static_feedbackContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback

elab "checked_actual_corrected_static_nineContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine).type
theorem checked_actual_corrected_static_nine : checked_actual_corrected_static_nineContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine

elab "checked_actual_static_current_circuitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit).type
theorem checked_actual_static_current_circuit : checked_actual_static_current_circuitContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit

elab "checked_actual_native_current_spatial_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return).type
theorem checked_actual_native_current_spatial_return : checked_actual_native_current_spatial_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return

elab "checked_actual_native_current_uniform_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price).type
theorem checked_actual_native_current_uniform_price : checked_actual_native_current_uniform_priceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price

elab "checked_actual_feedback_null_damping_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return).type
theorem checked_actual_feedback_null_damping_return : checked_actual_feedback_null_damping_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return

elab "checked_actual_feedback_null_spatial_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return).type
theorem checked_actual_feedback_null_spatial_return : checked_actual_feedback_null_spatial_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return

elab "checked_actual_feedback_null_source_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price).type
theorem checked_actual_feedback_null_source_price : checked_actual_feedback_null_source_priceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price

elab "checked_actual_longrange_coefficient_balanceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance).type
theorem checked_actual_longrange_coefficient_balance : checked_actual_longrange_coefficient_balanceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance

end LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit

open Lean Elab Command
private def packageCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def packageCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (packageCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def packageCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := packageCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_dressed_static_feedback" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticFeedback,`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticCurrentCircuit,`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticLongrangeReturn]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeCurrentRead,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.feedbackCurrentRead,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nullCurrentRead,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeCurrentCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeMatrixReader,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeCurrentPrice,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.zeroFeedbackNullRead,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.sourceFeedbackNullCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.sourceFeedbackNullPrice,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.SourceLongrangeReturn,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.sourceLongrangeReturn,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_static_ray,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_corrected_static_feedback,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_corrected_static_nine,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_static_current_circuit,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_native_current_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_native_current_uniform_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_feedback_null_damping_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_feedback_null_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_feedback_null_source_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit.checked_actual_longrange_coefficient_balance]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback,#[
    ``LowEnergy.GaussComposite.ActualDressedCorrectedGreen.actual_corrected_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray,
    ``LowEnergy.PreparationPhysicalVoltageCompleteReturn.sourceGreen_original_left]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine,#[
    ``LowEnergy.GaussComposite.ActualDressedCorrectedGreen.actual_corrected_response_equation,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit,#[
    ``LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.corrected_probe_read_original,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return,#[
    ``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceSpatialStaticNativeFieldResidue,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeCurrentCoefficient]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_domination,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.nativeMatrixReader]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return,#[
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.source_ordered_original_chart,
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.actual_zero_clock_probe,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return,#[
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.actual_ordered_coulomb_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price,#[
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.sourceFeedbackNullPrice]),
    (``LowEnergy.GaussComposite.ActualDressedStaticFeedback.sourceLongrangeReturn,#[
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.sourceOrderedStaticReturn,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedCorrectedGreen.actual_corrected_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.correctedProbeRead,
    ``LowEnergy.GaussComposite.ActualCompositeFieldCurrent.compositeCurrent,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequencyQuantumCorrection,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullCoordinates,
    ``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceSpatialSourceStaticRegular,
    ``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceSpatialStaticNativeFieldResidue,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_domination,
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.source_ordered_original_chart,
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.actual_zero_clock_probe,
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.actual_ordered_coulomb_return,
    ``LowEnergy.GaussComposite.ActualDressedOrderedStatic.sourceOrderedStaticReturn]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaques : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaques := opaques + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_STATIC_FEEDBACK_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"DRESSED_STATIC_FEEDBACK_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_static_feedback
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price
#print axioms LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance
