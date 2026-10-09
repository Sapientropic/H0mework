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

elab "#audit_dressed_half_ir" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfFeedback,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfSchur,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfPhysicalConsumer,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRAnalytic,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRFactor,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRReturn]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedback,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackDet,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackPrice,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfRegularRegion,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackResolvent,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfResponseNine,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfSchur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfSchurSource,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfWindowFeedback,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actualIRSourcePrice,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_feedback_regular_of_source_price,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_feedback_inverse_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_feedback_response,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_response_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_response_null_data,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_response_euler,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_schur_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_static_quantum_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_static_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_physical_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_window_feedback_limit,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_window_feedback_eventually_regular,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_half_window_feedback_inverse_limit,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_original_propagation_numerator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_original_source_regular_analytic,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_original_static_regular_operator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_sixth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_sixth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.checked_actual_sixth_ir_real_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.same_source_price_inverse_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.same_full_original_ir_factor,
    ``LowEnergy.GaussComposite.ActualDressedHalfIRAudit.same_actual_ir_real_return]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackPrice,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackDet]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackDet,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.halfFeedbackResolvent,
    ``Matrix.mul_nonsing_inv,
    ``Matrix.nonsing_inv_mul]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.original_forced_field]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return,#[
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressed_static_polarization_actual]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.damped_source_sheet_response,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequency_polarization_window_limit]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit]),
    (``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic,
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourcePole_regular]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price,#[
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressed_static_polarization_regularized]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressed_static_polarization_regularized]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization]),
    (``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular,
    ``LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.CanonicalCompletedSector.seed,
    ``LowEnergy.NativeHistoryGrade.projection,
    ``LowEnergy.GaussComposite.SourceGraph.prepared,
    ``LowEnergy.PreparationVacuumUncutYukawa.uncutOperator,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointCompression,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointCurrent,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherJet,
    ``LowEnergy.CanonicalPhysicalSpatial.compression,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointY_source,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleOrder,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleRegular,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.sourceNull,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullLift,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullCoordinates,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequencyQuantumCorrection,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequencyResponsePencil,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.staticQuantumCorrection,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.staticResponsePencil]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_HALF_IR_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_HALF_IR_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_half_ir
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_regular_of_source_price
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_inverse_generated
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_feedback_response
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_generated
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_null_data
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_response_euler
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_schur_generated
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_full_solution_schur
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_static_quantum_return
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.static_half_full_solution_schur
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.physical_half_full_solution_schur
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_limit
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_eventually_regular
#print axioms LowEnergy.GaussComposite.ActualDressedHalfGreenSchur.half_window_feedback_inverse_limit
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.original_propagation_numerator_analytic
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.original_source_regular_analytic
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.original_static_regular_operator_analytic
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_ir_source_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_real_price
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_order_lower
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_factor
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_regularization
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return
#print axioms LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_real_return
