import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantCurvature
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantPole

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMInvariantPoleAudit
elab "checked_native_curvature_gram_holonomicContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic).type
theorem checked_native_curvature_gram_holonomic : checked_native_curvature_gram_holonomicContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic

elab "checked_curvature_gram_first_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated).type
theorem checked_curvature_gram_first_generated : checked_curvature_gram_first_generatedContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated

elab "checked_curvature_gram_second_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated).type
theorem checked_curvature_gram_second_generated : checked_curvature_gram_second_generatedContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated

elab "checked_curvature_gram_and_original_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action).type
theorem checked_curvature_gram_and_original_action : checked_curvature_gram_and_original_actionContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action

elab "checked_curvature_pair_orbit_balanceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance).type
theorem checked_curvature_pair_orbit_balance : checked_curvature_pair_orbit_balanceContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance

elab "checked_invariant_curvature_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original).type
theorem checked_invariant_curvature_original : checked_invariant_curvature_originalContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original

elab "checked_invariant_curvature_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous).type
theorem checked_invariant_curvature_continuous : checked_invariant_curvature_continuousContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous

elab "checked_native_origin_curvature_orbitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit).type
theorem checked_native_origin_curvature_orbit : checked_native_origin_curvature_orbitContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit

elab "checked_native_origin_invariant_firstContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first).type
theorem checked_native_origin_invariant_first : checked_native_origin_invariant_firstContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first

elab "checked_invariant_origin_modeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode).type
theorem checked_invariant_origin_mode : checked_invariant_origin_modeContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode

elab "checked_invariant_origin_responseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response).type
theorem checked_invariant_origin_response : checked_invariant_origin_responseContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response

elab "checked_dressed_invariant_frequency_leadingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading).type
theorem checked_dressed_invariant_frequency_leading : checked_dressed_invariant_frequency_leadingContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open LowEnergy.CanonicalGradedSpatialSource LowEnergy.PreparationVacuumPhysicalFeedback
open LowEnergy.PreparationVacuumPhysicalCharacteristic LowEnergy.PreparationVacuumPhysicalPoleSheet
open LowEnergy.PreparationPhysicalNativePhotonFluxReturn
open LowEnergy.PreparationVacuumLowerClassical
open LowEnergy.SourcePropagationNativeActionHessian LowEnergy.PreparationVacuumMixedFieldReturn
open LowEnergy.GaussComposite.ActualEMInvariantCurvature LowEnergy.GaussComposite.ActualEMInvariantPole
open LowEnergy.GaussComposite.ActualEMGaugeCurvature LowEnergy.GaussComposite.ActualEMDressedGaugePole
open LowEnergy.GaussComposite.ActualDressedFullCoulomb LowEnergy.GaussComposite.ActualEMAction
open Filter
open scoped Matrix BigOperators Topology

attribute [local irreducible] dressedGaugePole sourceWholePhotonFrequencyResidue emActionFrequencyJet

theorem checked_same_invariant_action_flux (event : DressedEvent) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) (pair other : Fin 6) :
    ∀ᶠ e in scaleApproach,
      invariantCurvatureMap (frequencyRay e.val (sourceSheet branch n unit e.val) n) pair other
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          (emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *ᵥ
            dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T)) =
      invariantCurvatureMap (frequencyRay e.val (sourceSheet branch n unit e.val) n) pair other
        (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) := by
  filter_upwards [dressed_gauge_frequency_flux event branch n unit T] with e flux
  exact congrArg (invariantCurvatureMap _ pair other) flux

private theorem audit_vec3_last {α : Type} (a b c : α) : (![a,b,c] : Fin 3 → α) 2 = c := rfl

theorem checked_unit_direction : spatialSquare (![1,0,0] : PhysicalMomentum)=1 := by
  norm_num [spatialSquare,audit_vec3_last]

theorem checked_scale_nonempty : scaleApproach.NeBot := scaleApproach_nonempty
end LowEnergy.GaussComposite.ActualEMInvariantPoleAudit

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

elab "#audit_em_invariant_curvature_pole" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantCurvature,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantPole]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.complexGaugePair,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.nativeCurvatureGram,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvatureGramFirst,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvatureGramSecond,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariantCurvatureRead,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariantCurvatureMap,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_native_curvature_gram_holonomic,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_curvature_gram_first_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_curvature_gram_second_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_curvature_gram_and_original_action,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_curvature_pair_orbit_balance,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_invariant_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_invariant_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_native_origin_curvature_orbit,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_native_origin_invariant_first,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_invariant_origin_mode,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_invariant_origin_response,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_dressed_invariant_frequency_leading,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_same_invariant_action_flux,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_unit_direction,
    ``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_scale_nonempty]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic,#[
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeCurvature_generated,
    ``LowEnergy.SourcePropagationNativeActionHessian.rawGaugePair_source]),
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated,#[
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeRawCurvature_ray]),
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated,#[
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeRawCurvature_ray]),
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action,#[
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeDensity_second,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeQuadratic_flat]),
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance,#[
    ``SaturationMonoid.PhysicsCore.StageNineP286SourceRelativeWardAlgebra.p286LiePairing_bracket_left]),
    (``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original,#[
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit,#[
    ``LowEnergy.GaussComposite.ActualEMCompleteOrbit.native_origin_gauge_orbit]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first,#[
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode,#[
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response,#[
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading,#[
    ``LowEnergy.GaussComposite.ActualEMDressedTransferIR.dressed_soft_whole_pole,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous]),
    (``LowEnergy.GaussComposite.ActualEMInvariantPoleAudit.checked_same_invariant_action_flux,#[
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariantCurvatureMap])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response,
    ``LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeConfiguration,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeDensity,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeQuadratic,
    ``SaturationMonoid.PhysicsCore.StageNineP286GaugeAuxiliaryVariation.p286LiePairing,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.fullGaugeCurvature,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonFrequencyResidue]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_EM_INVARIANT_CURVATURE_POLE_AUDIT_OUTPUT") then
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
  logInfo m!"EM_INVARIANT_CURVATURE_POLE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_em_invariant_curvature_pole
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original
#print axioms LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous
#print axioms LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit
#print axioms LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first
#print axioms LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode
#print axioms LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response
#print axioms LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading
