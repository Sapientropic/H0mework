import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBoundary
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCauchy
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHistory

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

