import H0mework.Versions.X.NavierStokes.MaterialReadback.Material

set_option autoImplicit false
open scoped ContDiff

namespace SaturationMonoid.NavierStokes.NativeMaterialDifferential

open PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore NativeMaterialReadback

noncomputable section

private theorem split_fderiv {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (encode : F →L[ℝ] G) (decode : G →L[ℝ] F)
    (readback : ∀ value, decode (encode value) = value) (field : E → F) (point : E) :
    fderiv ℝ (encode ∘ field) point = encode.comp (fderiv ℝ field point) := by
  by_cases smooth : DifferentiableAt ℝ field point
  · exact (encode.hasFDerivAt.comp point smooth.hasFDerivAt).fderiv
  · have encoded : ¬ DifferentiableAt ℝ (encode ∘ field) point := by
      intro actual
      have recovered := decode.differentiableAt.comp point actual
      exact smooth (by simpa only [Function.comp_def, readback] using recovered)
    rw [fderiv_zero_of_not_differentiableAt encoded, fderiv_zero_of_not_differentiableAt smooth,
      ContinuousLinearMap.comp_zero]

/-- A source embedding with a fixed left inverse commutes with every iterated derivative,
including Lean's total derivative outside the differentiability locus. -/
private theorem split_iteratedFDeriv {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (encode : F →L[ℝ] G) (decode : G →L[ℝ] F)
    (readback : ∀ value, decode (encode value) = value)
    (field : E → F) (order : Nat) (point : E) :
    iteratedFDeriv ℝ order (encode ∘ field) point =
      encode.compContinuousMultilinearMap (iteratedFDeriv ℝ order field point) := by
  induction order generalizing point with
  | zero =>
    ext directions
    simp
  | succ order induction =>
    let liftedEncode := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin order => E) F G encode
    let liftedDecode := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin order => E) G F decode
    have liftedReadback (value : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) :
        liftedDecode (liftedEncode value) = value := by
      ext directions
      exact readback (value directions)
    have fields : iteratedFDeriv ℝ order (encode ∘ field) = liftedEncode ∘ iteratedFDeriv ℝ order field :=
      funext induction
    ext directions
    rw [iteratedFDeriv_succ_apply_left, fields,
      split_fderiv liftedEncode liftedDecode liftedReadback]
    rfl

theorem increment_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → PhysicalSpace) (order : Nat) (point : E) :
    iteratedFDeriv ℝ order (materialIncrement ∘ field) point =
      materialIncrement.compContinuousMultilinearMap (iteratedFDeriv ℝ order field point) :=
  split_iteratedFDeriv materialIncrement velocityRead velocityRead_increment field order point

theorem velocity_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → PhysicalSpace) (order : Nat) (point : E) :
    velocityRead.compContinuousMultilinearMap
      (iteratedFDeriv ℝ order (materialIncrement ∘ field) point) = iteratedFDeriv ℝ order field point := by
  rw [increment_iteratedFDeriv]
  ext1 directions
  exact velocityRead_increment _

theorem increment_contDiff_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → PhysicalSpace) (order : WithTop ℕ∞) :
    ContDiff ℝ order (materialIncrement ∘ field) ↔ ContDiff ℝ order field := by
  constructor
  · intro smooth
    have recovered := velocityRead.contDiff.comp smooth
    simpa only [Function.comp_def, velocityRead_increment] using recovered
  · exact materialIncrement.contDiff.comp

private theorem iterated_succ_const_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (field : E → F) (constant : F) (order : Nat) :
    iteratedFDeriv ℝ (order + 1) (fun point => constant + field point) = iteratedFDeriv ℝ (order + 1) field := by
  induction order with
  | zero =>
    funext point
    ext1 directions
    rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, fderiv_const_add]
  | succ order induction =>
    funext point
    ext1 directions
    rw [iteratedFDeriv_succ_apply_left, induction]
    rfl

theorem source_coordinate_eq (velocity : PhysicalSpace) :
    matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter velocity) =
      matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0) + materialIncrement velocity := by
  rw [materialIncrement_eq, ← add_sub_assoc, add_sub_cancel_left]

/-- All derivatives of the original complete matter field recover the same physical derivatives. -/
theorem material_jet_readback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → PhysicalSpace) (order : Nat) (point : E) :
    velocityRead.compContinuousMultilinearMap
      (iteratedFDeriv ℝ order (fun actual => matterCoordinateEquiv
        (NativeCanonicalFluidCoframe.matter (field actual))) point) = iteratedFDeriv ℝ order field point := by
  cases order with
  | zero =>
    ext1 directions
    exact velocityRead_matter (field point)
  | succ order =>
    have source : (fun actual => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter (field actual))) =
      fun actual => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0) + materialIncrement (field actual) :=
        funext fun actual => source_coordinate_eq (field actual)
    rw [source]
    rw [iterated_succ_const_add]
    exact velocity_iteratedFDeriv field (order + 1) point

theorem material_contDiff_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → PhysicalSpace) (order : WithTop ℕ∞) :
    ContDiff ℝ order (fun point => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter (field point))) ↔
      ContDiff ℝ order field := by
  constructor
  · intro smooth
    have recovered := velocityRead.contDiff.comp smooth
    simpa only [Function.comp_def, velocityRead_matter] using recovered
  · intro smooth
    have source : (fun actual => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter (field actual))) =
      fun actual => matterCoordinateEquiv (NativeCanonicalFluidCoframe.matter 0) + materialIncrement (field actual) :=
        funext fun actual => source_coordinate_eq (field actual)
    rw [source]
    exact contDiff_const.add (materialIncrement.contDiff.comp smooth)

end
end SaturationMonoid.NavierStokes.NativeMaterialDifferential
