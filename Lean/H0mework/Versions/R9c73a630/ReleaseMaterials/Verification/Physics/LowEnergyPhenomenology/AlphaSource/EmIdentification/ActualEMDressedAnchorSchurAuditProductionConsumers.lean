import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSourceAnchor
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedAnchorInverse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedConstraint
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit
elab "checked_material_kinematicsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics).type
theorem checked_material_kinematics : checked_material_kinematicsContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics

elab "checked_material_observer_unchangedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_observer_unchanged).type
theorem checked_material_observer_unchanged : checked_material_observer_unchangedContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_observer_unchanged

elab "checked_material_budget_nonnegativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_budget_nonnegative).type
theorem checked_material_budget_nonnegative : checked_material_budget_nonnegativeContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_budget_nonnegative

elab "checked_material_linear_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price).type
theorem checked_material_linear_price : checked_material_linear_priceContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price

elab "checked_material_constant_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price).type
theorem checked_material_constant_price : checked_material_constant_priceContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price

elab "checked_materialWindowBudget_nonnegativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget_nonnegative).type
theorem checked_materialWindowBudget_nonnegative : checked_materialWindowBudget_nonnegativeContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget_nonnegative

elab "checked_anchorExtra_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra_positive).type
theorem checked_anchorExtra_positive : checked_anchorExtra_positiveContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra_positive

elab "checked_anchorRadius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius_positive).type
theorem checked_anchorRadius_positive : checked_anchorRadius_positiveContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius_positive

elab "checked_anchor_window_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_factor).type
theorem checked_anchor_window_factor : checked_anchor_window_factorContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_factor

elab "checked_anchor_weighted_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_weighted_price).type
theorem checked_anchor_weighted_price : checked_anchor_weighted_priceContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_weighted_price

elab "checked_anchor_window_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source).type
theorem checked_anchor_window_source : checked_anchor_window_sourceContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source

elab "checked_anchor_feedback_coefficientContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient).type
theorem checked_anchor_feedback_coefficient : checked_anchor_feedback_coefficientContract := @LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient

elab "checked_anchor_window_operator_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_window_operator_price).type
theorem checked_anchor_window_operator_price : checked_anchor_window_operator_priceContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_window_operator_price

elab "checked_anchor_polarization_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price).type
theorem checked_anchor_polarization_price : checked_anchor_polarization_priceContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price

elab "checked_anchor_update_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price).type
theorem checked_anchor_update_price : checked_anchor_update_priceContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price

elab "checked_anchor_feedback_unitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit).type
theorem checked_anchor_feedback_unit : checked_anchor_feedback_unitContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit

elab "checked_anchor_inverse_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated).type
theorem checked_anchor_inverse_generated : checked_anchor_inverse_generatedContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated

elab "checked_anchor_feedback_responseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response).type
theorem checked_anchor_feedback_response : checked_anchor_feedback_responseContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response

elab "checked_anchor_inverse_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price).type
theorem checked_anchor_inverse_price : checked_anchor_inverse_priceContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price

elab "checked_anchor_actual_window_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_actual_window_inverse).type
theorem checked_anchor_actual_window_inverse : checked_anchor_actual_window_inverseContract := @LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_actual_window_inverse

elab "checked_source_null_projectionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection).type
theorem checked_source_null_projection : checked_source_null_projectionContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection

elab "checked_source_null_eulerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_euler).type
theorem checked_source_null_euler : checked_source_null_eulerContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_euler

elab "checked_source_null_greenContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green).type
theorem checked_source_null_green : checked_source_null_greenContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green

elab "checked_source_compatibility_eulerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler).type
theorem checked_source_compatibility_euler : checked_source_compatibility_eulerContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler

elab "checked_anchor_response_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated).type
theorem checked_anchor_response_generated : checked_anchor_response_generatedContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated

elab "checked_anchor_response_initialContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial).type
theorem checked_anchor_response_initial : checked_anchor_response_initialContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial

elab "checked_anchor_response_eulerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler).type
theorem checked_anchor_response_euler : checked_anchor_response_eulerContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler

elab "checked_anchor_solution_iffContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff).type
theorem checked_anchor_solution_iff : checked_anchor_solution_iffContract := @LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff

elab "checked_source_null_coordinates_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated).type
theorem checked_source_null_coordinates_generated : checked_source_null_coordinates_generatedContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated

elab "checked_source_null_lift_coordinatesContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_coordinates).type
theorem checked_source_null_lift_coordinates : checked_source_null_lift_coordinatesContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_coordinates

elab "checked_source_null_lift_fixedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed).type
theorem checked_source_null_lift_fixed : checked_source_null_lift_fixedContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed

elab "checked_source_compatibility_nineContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine).type
theorem checked_source_compatibility_nine : checked_source_compatibility_nineContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine

elab "checked_anchor_schur_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated).type
theorem checked_anchor_schur_generated : checked_anchor_schur_generatedContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated

elab "checked_anchor_full_solution_schurContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur).type
theorem checked_anchor_full_solution_schur : checked_anchor_full_solution_schurContract := @LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator PreparationVacuumGaugeSourceInjection
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open MeasureTheory
open scoped Matrix Interval
attribute [local irreducible] anchorEvent anchorFeedbackResolvent dressedWindowPolarization
  originalJacobi originalChange originalInverse originalReadback

private def originalWindowSource (event : DressedEvent) (a : SignalAmplitude) : SignalAmplitude :=
  fun i=>∫t in (0:ℝ)..anchorWindow event a,laplaceWeight 3 t*
    deriv (fun r=>dressedSignalRawEuler (anchorEvent event) 0 anchorInput a r t i) 0

-- The actual two-quadrature nonlinear source has a generated positive window and returns through the new inverse/Schur.
theorem checked_original_nonlinear_window_schur (event : DressedEvent) (a : SignalAmplitude) :
    ∃initial : Fin 9→ℂ,
      a=anchorResponseNine event (anchorWindow event a) (originalWindowSource event a) initial ∧
      anchorSchur event (anchorWindow event a)*ᵥinitial=
        anchorSchurSource event (anchorWindow event a) (originalWindowSource event a) := by
  obtain ⟨positive,small,inside⟩:=anchor_window_source event a
  apply (anchor_full_solution_schur event _ positive small _ a).mp
  exact (dressed_native_window_pencil_generated (anchorEvent event) 0 anchorInput 3
    (anchorWindow event a) positive.le a inside).symm

-- Arbitrary forcing retains every original null coordinate even before the Ward compatibility equations are solved.
theorem checked_arbitrary_nine_initial (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    sourceNullCoordinates anchorInput (anchorResponseNine event T forcing initial)=initial := by
  have response : anchorResponseNine event T forcing initial=
      anchorResponse event T forcing (sourceNullLift anchorInput initial) := by
    unfold anchorResponseNine anchorResponse
    rw [source_null_lift_fixed]
  have retained:=anchor_response_initial event T positive small forcing (sourceNullLift anchorInput initial)
  rw [source_null_lift_fixed] at retained
  have coordinates:=congrArg (sourceNullCoordinates anchorInput) retained
  rw [←source_null_coordinates_generated,source_null_lift_coordinates,source_null_lift_coordinates] at coordinates
  rwa [response]

theorem checked_actual_inverse_price (event : DressedEvent) (a : SignalAmplitude) (forcing : SignalAmplitude) :
    ‖anchorFeedbackResolvent event (anchorWindow event a)*ᵥforcing‖ ≤ (16/15:ℝ)*‖forcing‖ :=
  anchor_inverse_price event _ (anchor_window_source event a).1 (anchor_window_source event a).2.1 forcing

-- The unchanged actual observer is consumed at the material event used by the contraction proof.
theorem checked_actual_observer_unchanged (event : DressedEvent) : dressedEulerObserver (anchorEvent event)=dressedEulerObserver event := by
  unfold anchorEvent
  exact material_observer_unchanged event _ _


theorem checked_positive_inverse_domain : (0:ℝ)<1/2 ∧ (1/2:ℝ)≤1 := by norm_num
theorem checked_zero_window_excluded : ¬(0:ℝ)<0 := by norm_num
theorem checked_nine_lift_nonempty : ∃x : Fin 9→ℂ, x≠0 := by
  refine ⟨fun _=>1,?_⟩
  intro z
  have bad:=congrFun z (0:Fin 9)
  norm_num at bad
end LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit

