import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBackground
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHalfIntegral
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearHalfResponse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearPolarization

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit
elab "checked_noether_background_initial_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source).type
theorem checked_noether_background_initial_source : checked_noether_background_initial_sourceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source

elab "checked_noether_background_initial_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2).type
theorem checked_noether_background_initial_C2 : checked_noether_background_initial_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2

elab "checked_noether_background_initial_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative).type
theorem checked_noether_background_initial_derivative : checked_noether_background_initial_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative

elab "checked_noether_background_operator_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2).type
theorem checked_noether_background_operator_C2 : checked_noether_background_operator_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2

elab "checked_noether_background_operator_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source).type
theorem checked_noether_background_operator_source : checked_noether_background_operator_sourceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source

elab "checked_noether_background_operator_pencilContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil).type
theorem checked_noether_background_operator_pencil : checked_noether_background_operator_pencilContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil

elab "checked_noether_background_operator_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative).type
theorem checked_noether_background_operator_derivative : checked_noether_background_operator_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative

elab "checked_noether_nonlinear_kernel_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual).type
theorem checked_noether_nonlinear_kernel_actual : checked_noether_nonlinear_kernel_actualContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual

elab "checked_noether_nonlinear_half_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable).type
theorem checked_noether_nonlinear_half_integrable : checked_noether_nonlinear_half_integrableContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable

elab "checked_noether_nonlinear_half_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background).type
theorem checked_noether_nonlinear_half_background : checked_noether_nonlinear_half_backgroundContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background

elab "checked_noether_nonlinear_half_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2).type
theorem checked_noether_nonlinear_half_C2 : checked_noether_nonlinear_half_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2

elab "checked_noether_nonlinear_half_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative).type
theorem checked_noether_nonlinear_half_derivative : checked_noether_nonlinear_half_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative

elab "checked_noether_nonlinear_weighted_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price).type
theorem checked_noether_nonlinear_weighted_price : checked_noether_nonlinear_weighted_priceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price

elab "checked_noether_nonlinear_half_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail).type
theorem checked_noether_nonlinear_half_tail : checked_noether_nonlinear_half_tailContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail

elab "checked_dressed_noether_half_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable).type
theorem checked_dressed_noether_half_integrable : checked_dressed_noether_half_integrableContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable

elab "checked_dressed_noether_half_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read).type
theorem checked_dressed_noether_half_read : checked_dressed_noether_half_readContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read

elab "checked_dressed_noether_window_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read).type
theorem checked_dressed_noether_window_read : checked_dressed_noether_window_readContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read

elab "checked_dressed_noether_half_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background).type
theorem checked_dressed_noether_half_background : checked_dressed_noether_half_backgroundContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background

elab "checked_dressed_noether_half_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2).type
theorem checked_dressed_noether_half_C2 : checked_dressed_noether_half_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2

elab "checked_dressed_noether_half_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative).type
theorem checked_dressed_noether_half_derivative : checked_dressed_noether_half_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative

elab "checked_dressed_noether_half_column_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative).type
theorem checked_dressed_noether_half_column_derivative : checked_dressed_noether_half_column_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative

elab "checked_dressed_noether_half_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail).type
theorem checked_dressed_noether_half_tail : checked_dressed_noether_half_tailContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail

elab "checked_dressed_noether_half_fderivContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv).type
theorem checked_dressed_noether_half_fderiv : checked_dressed_noether_half_fderivContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv

elab "checked_dressed_noether_half_full_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative).type
theorem checked_dressed_noether_half_full_derivative : checked_dressed_noether_half_full_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative

elab "checked_dressed_normalized_noether_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative).type
theorem checked_dressed_normalized_noether_derivative : checked_dressed_normalized_noether_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse ActualDressedNonlinearHalf
open Filter
open scoped Topology Matrix

theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon:=1
    precision:=by norm_num
    momentum:=0
    frame:=Classical.choice inferInstance
    cut:=0
    energy:=Complex.I
    nonreal:=by simp}⟩

/-- The actual nonlinear halfline has a source-generated common field neighborhood. -/
theorem checked_actual_half_common_neighborhood (event : DressedEvent) :
    ∃radius : ℝ,0<radius ∧ ∀h : Field289,‖h‖<radius→
      dressedNoetherHalfSource event 0 1 h=dressedNoetherBackgroundSource event 0 1 h := by
  have source:=dressed_noether_half_background event 0 1 (by norm_num)
  obtain ⟨radius,positive,inside⟩:=Metric.mem_nhds_iff.mp source
  refine ⟨radius,positive,fun h bound=>inside ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right] using bound

/-- A nonzero original field slot is consumed at an independent positive observation clock. -/
theorem checked_actual_normalized_field_direction (event : DressedEvent) :
    HasDerivAt (fun r : ℝ=>dressedNormalizedNoetherSource event 0 2 (r • fieldUnit 20))
      (staticQuantumCorrection event 0 2*ᵥ(fun j=>(fieldUnit 20 j:ℂ))) 0 :=
  dressed_normalized_noether_derivative event 0 2 (by norm_num) (fieldUnit 20)

end LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit

