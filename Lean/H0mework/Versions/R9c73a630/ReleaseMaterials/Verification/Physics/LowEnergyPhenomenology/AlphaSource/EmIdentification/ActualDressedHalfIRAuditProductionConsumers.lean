import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfFeedback
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfSchur
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfPhysicalConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRAnalytic
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRFactor
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRReturn

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedHalfIRAudit
elab "checked_half_feedback_regular_of_source_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price).type
theorem checked_half_feedback_regular_of_source_price : checked_half_feedback_regular_of_source_priceContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price

elab "checked_half_feedback_inverse_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated).type
theorem checked_half_feedback_inverse_generated : checked_half_feedback_inverse_generatedContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated

elab "checked_half_feedback_responseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response).type
theorem checked_half_feedback_response : checked_half_feedback_responseContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response

elab "checked_half_response_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated).type
theorem checked_half_response_generated : checked_half_response_generatedContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated

elab "checked_half_response_null_dataContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data).type
theorem checked_half_response_null_data : checked_half_response_null_dataContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data

elab "checked_half_response_eulerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler).type
theorem checked_half_response_euler : checked_half_response_eulerContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler

elab "checked_half_schur_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated).type
theorem checked_half_schur_generated : checked_half_schur_generatedContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated

elab "checked_half_full_solution_schurContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur).type
theorem checked_half_full_solution_schur : checked_half_full_solution_schurContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur

elab "checked_half_static_quantum_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return).type
theorem checked_half_static_quantum_return : checked_half_static_quantum_returnContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return

elab "checked_static_half_full_solution_schurContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur).type
theorem checked_static_half_full_solution_schur : checked_static_half_full_solution_schurContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur

elab "checked_physical_half_full_solution_schurContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur).type
theorem checked_physical_half_full_solution_schur : checked_physical_half_full_solution_schurContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur

elab "checked_half_window_feedback_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit).type
theorem checked_half_window_feedback_limit : checked_half_window_feedback_limitContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit

elab "checked_half_window_feedback_eventually_regularContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular).type
theorem checked_half_window_feedback_eventually_regular : checked_half_window_feedback_eventually_regularContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular

elab "checked_half_window_feedback_inverse_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit).type
theorem checked_half_window_feedback_inverse_limit : checked_half_window_feedback_inverse_limitContract := @LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit

elab "checked_original_propagation_numerator_analyticContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic).type
theorem checked_original_propagation_numerator_analytic : checked_original_propagation_numerator_analyticContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic

elab "checked_original_source_regular_analyticContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic).type
theorem checked_original_source_regular_analytic : checked_original_source_regular_analyticContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic

elab "checked_original_static_regular_operator_analyticContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic).type
theorem checked_original_static_regular_operator_analytic : checked_original_static_regular_operator_analyticContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic

elab "checked_actual_regular_matrix_analyticContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic).type
theorem checked_actual_regular_matrix_analytic : checked_actual_regular_matrix_analyticContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic

elab "checked_actual_ir_source_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_ir_source_price_nonneg).type
theorem checked_actual_ir_source_price_nonneg : checked_actual_ir_source_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_ir_source_price_nonneg

elab "checked_actual_regular_matrix_real_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price).type
theorem checked_actual_regular_matrix_real_price : checked_actual_regular_matrix_real_priceContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price

elab "checked_actual_regular_matrix_order_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower).type
theorem checked_actual_regular_matrix_order_lower : checked_actual_regular_matrix_order_lowerContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower

elab "checked_actual_regular_matrix_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor).type
theorem checked_actual_regular_matrix_factor : checked_actual_regular_matrix_factorContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor

elab "checked_actual_sixth_ir_regularizationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization).type
theorem checked_actual_sixth_ir_regularization : checked_actual_sixth_ir_regularizationContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization

elab "checked_actual_sixth_ir_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return).type
theorem checked_actual_sixth_ir_return : checked_actual_sixth_ir_returnContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return

elab "checked_actual_sixth_ir_real_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return).type
theorem checked_actual_sixth_ir_real_return : checked_actual_sixth_ir_real_returnContract := @LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedHalfGreenSchur
open ActualEMDressedConstraint ActualEMDressedSchur ActualDressedFrequencyHalf
open ActualDressedIRReturn ActualDressedSylvester ActualDressedStaticPole
open Filter Set
open scoped Matrix Topology Matrix.Norms.Elementwise

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro zero
  have source:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at source
  exact zero_ne_one source

theorem same_source_price_inverse_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (small : halfFeedbackPrice event transfer p lambda<1) :
    halfFeedback event transfer p lambda*halfFeedbackResolvent event transfer p lambda=1 ∧
      halfFeedbackResolvent event transfer p lambda*halfFeedback event transfer p lambda=1 :=
  half_feedback_inverse_generated event transfer p lambda
    (half_feedback_regular_of_source_price event transfer p lambda small)

theorem same_full_original_ir_factor (event : DressedEvent) :
    ∃G : ℂ→Matrix (Fin 289) (Fin 289) ℂ,AnalyticAt ℂ G 0 ∧
      ∀ᶠz : ℂ in 𝓝 0,dressedStaticPoleRegular event z=z^(2*dressedStaticPoleOrder event-6) • G z :=
  actual_regular_matrix_factor event

theorem same_actual_ir_real_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,
      Tendsto (fun s : ℝ=>(s:ℂ)^6 • dressedStaticPolarization event 0 (s:ℂ))
        (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 L) :=
  actual_sixth_ir_real_return event
end LowEnergy.GaussComposite.ActualDressedHalfIRAudit

