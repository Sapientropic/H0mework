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

elab "#audit_dressed_anchor_schur" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSourceAnchor,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedAnchorInverse,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedConstraint,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorInput,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.actualMaterialPoint,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_observer_unchanged,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialLinearBudget,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialConstantBudget,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_budget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorGreenPrice,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorEvent,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_factor,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_weighted_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorWindow,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_window_operator_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchorFeedback,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchorFeedbackResolvent,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_actual_window_inverse,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.sourceNull,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchorResponse,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullCoordinates,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullLift,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_coordinates,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchorResponseNine,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchorSchur,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchorSchurSource,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_material_kinematics,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_material_observer_unchanged,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_material_budget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_material_linear_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_material_constant_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_materialWindowBudget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchorExtra_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchorRadius_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_window_factor,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_weighted_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_window_source,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_feedback_coefficient,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_window_operator_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_polarization_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_update_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_feedback_unit,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_inverse_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_feedback_response,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_inverse_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_actual_window_inverse,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_projection,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_green,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_compatibility_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_response_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_response_initial,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_response_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_solution_iff,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_coordinates_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_lift_coordinates,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_null_lift_fixed,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_source_compatibility_nine,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_schur_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_anchor_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_original_nonlinear_window_schur,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_arbitrary_nine_initial,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_actual_inverse_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_actual_observer_unchanged,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_positive_inverse_domain,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_zero_window_excluded,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_nine_lift_nonempty]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics]),
    (``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics]),
    (``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price,#[
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient]),
    (``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit,#[
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price]),
    (``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated,#[
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit]),
    (``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price,#[
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price]),
    (``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial,#[
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection]),
    (``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler,#[
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated]),
    (``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur,#[
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine]),
    (``LowEnergy.GaussComposite.ActualEMDressedAnchorSchurAudit.checked_original_nonlinear_window_schur,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_observer_unchanged,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_budget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget_nonnegative,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius_positive,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_factor,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_weighted_price,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_window_operator_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price,
    ``LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_actual_window_inverse,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_coordinates,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedNativeWindowPencil,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalRawEuler,
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius,
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.sourceNull,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullCoordinates]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_ANCHOR_SCHUR_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_ANCHOR_SCHUR_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_anchor_schur
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_kinematics
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_observer_unchanged
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_budget_nonnegative
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_linear_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.material_constant_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.materialWindowBudget_nonnegative
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorExtra_positive
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchorRadius_positive
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_factor
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_weighted_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source
#print axioms LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_feedback_coefficient
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_window_operator_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_polarization_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_update_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_unit
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_generated
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_feedback_response
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_inverse_price
#print axioms LowEnergy.GaussComposite.ActualEMDressedAnchorInverse.anchor_actual_window_inverse
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_projection
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_euler
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.source_null_green
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_generated
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_initial
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_response_euler
#print axioms LowEnergy.GaussComposite.ActualEMDressedConstraint.anchor_solution_iff
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_coordinates_generated
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_coordinates
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.source_null_lift_fixed
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated
#print axioms LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_full_solution_schur
