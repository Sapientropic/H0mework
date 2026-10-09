import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalNormalization
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit
elab "checked_original_temporal_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action).type
theorem checked_original_temporal_action : checked_original_temporal_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action

elab "checked_canonical_temporal_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action).type
theorem checked_canonical_temporal_action : checked_canonical_temporal_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action

elab "checked_canonical_temporal_quantizedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized).type
theorem checked_canonical_temporal_quantized : checked_canonical_temporal_quantizedContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized

elab "checked_temporal_action_fiberContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber).type
theorem checked_temporal_action_fiber : checked_temporal_action_fiberContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber

elab "checked_temporal_action_formContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form).type
theorem checked_temporal_action_form : checked_temporal_action_formContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form

elab "checked_temporal_action_global_readerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader).type
theorem checked_temporal_action_global_reader : checked_temporal_action_global_readerContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader

elab "checked_temporal_action_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable).type
theorem checked_temporal_action_integrable : checked_temporal_action_integrableContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable

elab "checked_em_action_fiberContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber).type
theorem checked_em_action_fiber : checked_em_action_fiberContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber

elab "checked_em_action_formContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form).type
theorem checked_em_action_form : checked_em_action_formContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form

elab "checked_em_action_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable).type
theorem checked_em_action_integrable : checked_em_action_integrableContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable

elab "checked_dressed_temporal_action_integralContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral).type
theorem checked_dressed_temporal_action_integral : checked_dressed_temporal_action_integralContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral

elab "checked_dressed_temporal_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit).type
theorem checked_dressed_temporal_action_limit : checked_dressed_temporal_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit

elab "checked_original_temporal_weight_coreContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core).type
theorem checked_original_temporal_weight_core : checked_original_temporal_weight_coreContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core

elab "checked_temporal_raw_noether_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return).type
theorem checked_temporal_raw_noether_return : checked_temporal_raw_noether_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return

elab "checked_actual_temporal_Y_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit).type
theorem checked_actual_temporal_Y_action_limit : checked_actual_temporal_Y_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit

elab "checked_temporal_noether_reader_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return).type
theorem checked_temporal_noether_reader_return : checked_temporal_noether_reader_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return

elab "checked_dressed_em_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit).type
theorem checked_dressed_em_action_limit : checked_dressed_em_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open ActualDressedTemporalCurrent
theorem checked_actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [h,norm_zero] at paid
  exact zero_ne_one paid

theorem checked_actual_Y_action_visible (event : DressedEvent) :
    ∀ᶠ readFrame : GaussUnitaryHistory.Index in GaussUnitaryHistory.sourceFilter,
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))-
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))≠0 := by
  exact (actual_temporal_Y_action_limit event).eventually_ne (by norm_num)

theorem checked_Y_input_nonzero (event : DressedEvent) :
    ActualDressedYJoint.dressedYInput event≠0 := by
  rw [ActualDressedYNoether.actual_Y_input_return]
  intro h
  have zero : sourceDressedUnit event.epsilon event.precision=0 := neg_eq_zero.mp h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at paid
  exact zero_ne_one paid

end LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit

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

elab "#audit_dressed_temporal_normalization" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalNormalization,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporalActionForm,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.emActionForm,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressedTemporalActionIntegral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressedEMActionIntegral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressedEMActionResponse,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_original_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_canonical_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_canonical_temporal_quantized,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_action_global_reader,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_em_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_em_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_em_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_dressed_temporal_action_integral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_dressed_temporal_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_original_temporal_weight_core,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_raw_noether_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_actual_temporal_Y_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_temporal_noether_reader_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_dressed_em_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_actual_Y_action_visible,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit.checked_Y_input_nonzero]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action,#[
    ``LowEnergy.PreparationVacuumActionFieldLift.rawActionSymbol_source,
    ``LowEnergy.PreparationVacuumActionFieldLift.symbolFirst_field]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedActionPhase.canonical_phase_time_weight]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber,#[
    ``LowEnergy.GaussComposite.ActualDressedActionPhase.canonical_em_quantized_return]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral,
    ``LowEnergy.GaussComposite.ActualDressedJointTemporal.dressed_temporal_response_limit]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.weightedTemporalForm_core,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeCore_source]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.temporalReader_projected_action,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeCore_source]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressedEMActionIntegral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressedEMActionResponse])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussHistoryHilbert.configurationMeasure,
    ``LowEnergy.PreparationVacuumSourceFieldFamily.sourceState,
    ``LowEnergy.PreparationPhysicalActionUnits.sourceTimeWeightCore,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.CanonicalPhysicalYResolvent.finiteFull]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_TEMPORAL_NORMALIZATION_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_TEMPORAL_NORMALIZATION_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_temporal_normalization
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit
