import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBoundary
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCauchy
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHistory

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoetherAudit
elab "checked_dressed_kinematic_transferContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer).type
theorem checked_dressed_kinematic_transfer : checked_dressed_kinematic_transferContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer

elab "checked_dressed_euler_observer_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original).type
theorem checked_dressed_euler_observer_original : checked_dressed_euler_observer_originalContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original

elab "checked_dressed_noether_jet_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated).type
theorem checked_dressed_noether_jet_generated : checked_dressed_noether_jet_generatedContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated

elab "checked_dressed_noether_jet_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous).type
theorem checked_dressed_noether_jet_continuous : checked_dressed_noether_jet_continuousContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous

elab "checked_dressed_noether_jet_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original).type
theorem checked_dressed_noether_jet_original : checked_dressed_noether_jet_originalContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original

elab "checked_dressed_noether_forcing_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_forcing_original).type
theorem checked_dressed_noether_forcing_original : checked_dressed_noether_forcing_originalContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_forcing_original

elab "checked_dressed_noether_field_equationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation).type
theorem checked_dressed_noether_field_equation : checked_dressed_noether_field_equationContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation

elab "checked_dressed_voltage_update_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original).type
theorem checked_dressed_voltage_update_original : checked_dressed_voltage_update_originalContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original

elab "checked_dressed_noether_history_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return).type
theorem checked_dressed_noether_history_return : checked_dressed_noether_history_returnContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return

elab "checked_dressed_noether_action_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative).type
theorem checked_dressed_noether_action_derivative : checked_dressed_noether_action_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative

elab "checked_dressed_noether_readbackContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback).type
theorem checked_dressed_noether_readback : checked_dressed_noether_readbackContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback

elab "checked_dressed_noether_field_cosourcesContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources).type
theorem checked_dressed_noether_field_cosources : checked_dressed_noether_field_cosourcesContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources

elab "checked_dressed_voltage_quantum_cosourcesContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources).type
theorem checked_dressed_voltage_quantum_cosources : checked_dressed_voltage_quantum_cosourcesContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources

elab "checked_dressed_voltage_update_splitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split).type
theorem checked_dressed_voltage_update_split : checked_dressed_voltage_update_splitContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split

elab "checked_dressed_voltage_curvature_updateContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update).type
theorem checked_dressed_voltage_curvature_update : checked_dressed_voltage_curvature_updateContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update

elab "checked_dressed_history_duration_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive).type
theorem checked_dressed_history_duration_positive : checked_dressed_history_duration_positiveContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive

elab "checked_dressed_nonlinear_source_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated).type
theorem checked_dressed_nonlinear_source_generated : checked_dressed_nonlinear_source_generatedContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated

elab "checked_dressed_history_forcing_noetherContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether).type
theorem checked_dressed_history_forcing_noether : checked_dressed_history_forcing_noetherContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether

elab "checked_dressed_voltage_duration_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive).type
theorem checked_dressed_voltage_duration_positive : checked_dressed_voltage_duration_positiveContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive

elab "checked_dressed_voltage_forcing_nonlinearContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear).type
theorem checked_dressed_voltage_forcing_nonlinear : checked_dressed_voltage_forcing_nonlinearContract := @LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourcePreparedResponse SourcePropagationNoetherTime
open ActualDressedSourcePreparation ActualDressedFullCoulomb ActualEMCauchyDynamic
open SourceGraph MeasureTheory Filter
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumFullFieldRiesz
open PreparationVacuumNoetherChart SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open ActualDressedFullCoulomb
open ActualDressedSourcePreparation PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb MeasureTheory Filter
open PreparationVacuumFieldConstraintResponse
open ActualDressedFullCoulomb ActualEMCauchyDynamic MeasureTheory Filter
open SourcePropagationNativeEulerHistory ActualDressedFullCoulomb ActualEMCauchyDynamic
open MeasureTheory Filter Set
open ActualDressedNoether ActualDressedSourceResponse CanonicalGradedCharge
open scoped Matrix BigOperators InnerProductSpace Topology Interval
attribute [local irreducible] dressedEulerObserver dressedNoetherJet dressedNoetherKernel
  dressedNonlinearSource dressedVoltageDuration sourceDressedUnit sourceProfile
  originalJacobi originalReadback originalChange sourceGreen
  PreparationVacuumOriginalGreenFeedback.sourceField

private theorem voltage_history_smooth (spatial : Fin 3→ℂ) (imaginary : Bool) :
    ContDiffAt ℝ 1 (fun t=>(voltageNativeTimeJet spatial imaginary t).value) 0 := by
  unfold voltageNativeTimeJet
  exact (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))

theorem actual_observer_nativeY_unit (event : DressedEvent) :
    dressedEulerObserver event (chargeReader nativeY)=1 := by
  rw [dressed_euler_observer_original]
  have paid:=source_dressed_connected_native_charge event.epsilon event.precision
  linear_combination -paid

theorem actual_observer_nativeY_nonzero (event : DressedEvent) :
    dressedEulerObserver event (chargeReader nativeY)≠0 := by
  rw [actual_observer_nativeY_unit]
  norm_num

theorem actual_nonlinear_window_nonempty (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∃ T : ℝ,0<T ∧ T<dressedVoltageDuration event transfer := by
  exact ⟨dressedVoltageDuration event transfer/2,half_pos (dressed_voltage_duration_positive event transfer),
    half_lt_self (dressed_voltage_duration_positive event transfer)⟩

theorem actual_zero_observation_window (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : ℂ) :
    dressedNoetherForcing event transfer signal lambda 0=0 := by
  ext i
  simp only [dressedNoetherForcing,intervalIntegral.integral_same,Pi.zero_apply]


theorem checked_transfer_not_reflected (event : DressedEvent) :
    LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer
      ((dressedKinematicPoint event (![1,0,0])).p+(dressedKinematicPoint event (![1,0,0])).k)
      (dressedKinematicPoint event (![1,0,0])).p ≠ -(![1,0,0] : PhysicalMomentum) := by
  rw [dressed_kinematic_transfer]
  intro bad
  have row:=congrFun bad 0
  norm_num at row
end LowEnergy.GaussComposite.ActualDressedNoetherAudit

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

elab "#audit_dressed_noether" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse,`H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction,`H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBoundary,`H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCauchy,`H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHistory]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedKinematicPoint,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherJet,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherForcing,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_forcing_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherField,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedVoltageForcing,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedVoltageUpdate,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherTimeSource,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherBoundary,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedHistoryDuration,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNonlinearSource,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedHistoryForcing,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedVoltageDuration,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_kinematic_transfer,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_euler_observer_original,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_jet_continuous,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_jet_original,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_forcing_original,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_field_equation,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_update_original,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_history_return,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_readback,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_noether_field_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_quantum_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_update_split,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_curvature_update,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_history_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_nonlinear_source_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_history_forcing_noether,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_dressed_voltage_forcing_nonlinear,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.actual_observer_nativeY_unit,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.actual_observer_nativeY_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.actual_nonlinear_window_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.actual_zero_observation_window,
    ``LowEnergy.GaussComposite.ActualDressedNoetherAudit.checked_transfer_not_reflected]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer,#[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original,#[
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated,#[
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous,#[
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet_continuous,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation,#[
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.original_forced_field]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original,#[
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.original_forced_field]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return,#[
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet_value,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.PreparationVacuumRawJointFeedback.rawReaderContact]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative,#[
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet_value,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_timejet_continuous,
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_timejet_generated]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split,#[
    ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_window_green,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedVoltageForcing,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherField]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split,
    ``LowEnergy.PreparationVacuumFieldConstraintResponse.originalReader36]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive,#[
    ``LowEnergy.SourcePropagationNativeEulerHistory.preparedHistoryDuration_positive]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated,#[
    ``LowEnergy.SourcePropagationNativeEulerHistory.actualPreparedHistoryKernel_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive]),
    (``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_forcing_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet,
    ``LowEnergy.SourcePropagationNativeEulerHistory.actualPreparedHistoryKernel,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime,
    ``LowEnergy.PreparationVacuumRawJointFeedback.rawReaderContact,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.PreparationVacuumFieldConstraintResponse.originalReader36]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_NOETHER_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_NOETHER_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_noether
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_kinematic_transfer
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_generated
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_forcing_original
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_equation
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_original
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_history_return
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_readback
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_field_cosources
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_quantum_cosources
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_update_split
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_curvature_update
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_duration_positive
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_history_forcing_noether
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_duration_positive
#print axioms LowEnergy.GaussComposite.ActualDressedNoether.dressed_voltage_forcing_nonlinear
