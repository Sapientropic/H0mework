import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyPolarization
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMGaugeCurvature
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit
elab "checked_voltage_transverse_exactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact).type
theorem checked_voltage_transverse_exact : checked_voltage_transverse_exactContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact

elab "checked_voltage_initial_transverse_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir).type
theorem checked_voltage_initial_transverse_ir : checked_voltage_initial_transverse_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir

elab "checked_voltage_magnetic_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir).type
theorem checked_voltage_magnetic_ir : checked_voltage_magnetic_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir

elab "checked_voltage_initial_magnetic_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir).type
theorem checked_voltage_initial_magnetic_ir : checked_voltage_initial_magnetic_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir

elab "checked_full_gauge_curvature_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original).type
theorem checked_full_gauge_curvature_original : checked_full_gauge_curvature_originalContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original

elab "checked_full_gauge_curvature_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative).type
theorem checked_full_gauge_curvature_derivative : checked_full_gauge_curvature_derivativeContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative

elab "checked_full_gauge_curvature_holonomicContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic).type
theorem checked_full_gauge_curvature_holonomic : checked_full_gauge_curvature_holonomicContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic

elab "checked_full_gauge_curvature_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous).type
theorem checked_full_gauge_curvature_continuous : checked_full_gauge_curvature_continuousContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous

elab "checked_full_gauge_bf_hessianContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian).type
theorem checked_full_gauge_bf_hessian : checked_full_gauge_bf_hessianContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian

elab "checked_full_gauge_cauchy_eventContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event).type
theorem checked_full_gauge_cauchy_event : checked_full_gauge_cauchy_eventContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event

elab "checked_dressed_voltage_spectral_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous).type
theorem checked_dressed_voltage_spectral_continuous : checked_dressed_voltage_spectral_continuousContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous

elab "checked_dressed_gauge_clockContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock).type
theorem checked_dressed_gauge_clock : checked_dressed_gauge_clockContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock

elab "checked_dressed_gauge_field_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original).type
theorem checked_dressed_gauge_field_original : checked_dressed_gauge_field_originalContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original

elab "checked_dressed_gauge_classical_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole).type
theorem checked_dressed_gauge_classical_pole : checked_dressed_gauge_classical_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole

elab "checked_dressed_gauge_frequency_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole).type
theorem checked_dressed_gauge_frequency_pole : checked_dressed_gauge_frequency_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole

elab "checked_dressed_gauge_curvature_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole).type
theorem checked_dressed_gauge_curvature_pole : checked_dressed_gauge_curvature_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole

elab "checked_dressed_gauge_frequency_fluxContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux).type
theorem checked_dressed_gauge_frequency_flux : checked_dressed_gauge_frequency_fluxContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux

open SaturationMonoid.PhysicsCore
open LowEnergy.GaussComposite.ActualEMCauchyDynamic LowEnergy.GaussComposite.ActualEMGaugeCurvature
open LowEnergy.GaussComposite.ActualEMDressedGaugePole
open LowEnergy.PreparationVacuumPhysicalCharacteristic LowEnergy.PreparationVacuumPhysicalFeedback
open LowEnergy.CanonicalGradedSpatialSource
open scoped Matrix BigOperators Topology

theorem checked_scale_nonempty : scaleApproach.NeBot := scaleApproach_nonempty

theorem checked_full_curvature_channels : Fintype.card (Fin 6 × Fin 12) = 72 := by decide

theorem checked_restricted_channels_distinct : Fintype.card (Fin 6 × Fin 12) ≠ 36 := by decide

theorem checked_transverse_not_arbitrary_zero :
    voltageTransverseRead (![1,0,0]) (![0,1,0]) 0 1 = 1 := by
  norm_num [voltageTransverseRead]

theorem checked_imaginary_jet_not_real :
    (gaugeFourierJet 0 (fun _ => Complex.I) true).1 0 ≠
      (gaugeFourierJet 0 (fun _ => Complex.I) false).1 0 := by
  norm_num [gaugeFourierJet]
end LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit

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

elab "#audit_full_gauge_dressed_pole" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyPolarization,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMGaugeCurvature,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltageTransverseRead,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltageYMagneticPair,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.gaugeFourierJet,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.fullGaugeRead,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.fullGaugeCurvature,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressedGaugeMomentum,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressedGaugeCurrent,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressedGaugeForcing,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressedGaugeField,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressedGaugePole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_voltage_transverse_exact,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_voltage_initial_transverse_ir,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_voltage_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_voltage_initial_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_curvature_derivative,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_curvature_holonomic,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_bf_hessian,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_gauge_cauchy_event,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_voltage_spectral_continuous,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_clock,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_field_original,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_classical_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_frequency_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_curvature_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_dressed_gauge_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_scale_nonempty,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_full_curvature_channels,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_restricted_channels_distinct,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_transverse_not_arbitrary_zero,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit.checked_imaginary_jet_not_real]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_y_frequency_electric]),
    (``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_electric_ir]),
    (``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_emitter_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_pole_factor]),
    (``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative,#[
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeRawCurvature_ray]),
    (``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic,#[
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeCurvature_generated]),
    (``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian,#[
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeQuadratic_flat]),
    (``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_same_green_response]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_timejet_continuous]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original,#[
    ``LowEnergy.PreparationVacuumNativePoleTensor.nativeResponse_original]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_window_action,
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_homogeneous]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole,#[
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonGreen_frequencyResidue]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole,#[
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous]),
    (``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_frequencyFlux])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian,
    ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole,
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeConfiguration,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeGaugeQuadratic,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
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
  if let some path ← liftIO (IO.getEnv "ALPHA_FULL_GAUGE_DRESSED_POLE_AUDIT_OUTPUT") then
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
  logInfo m!"FULL_GAUGE_DRESSED_POLE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_full_gauge_dressed_pole
#print axioms LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact
#print axioms LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir
#print axioms LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir
#print axioms LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian
#print axioms LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole
#print axioms LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux
