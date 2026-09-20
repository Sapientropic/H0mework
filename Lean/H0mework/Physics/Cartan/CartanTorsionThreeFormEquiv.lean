import H0mework.Physics.Cartan.CartanTorsionThreeFormCoordinates

/-!
# Nondegenerate Cartan torsion--three-form equivalence

For a nondegenerate coframe this module constructs the explicit inverse of
the existing KIN-1 response

`T -> star_I (T wedge e)`.

The inverse first applies the fixed Lorentzian internal undual, contracts the
result with the computed matrix inverse of the coframe, and removes the
four-dimensional trace with the uniquely forced factor `1/4`.  The
constructor accepts no action, source, residual, response witness,
normalization, branch receipt, stationarity certificate, or target solution.

This is a pointwise kinematic equivalence.  It does not yet generate a spin
current, contorsion, Levi--Civita baseline, full connection, local field, or
stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCartanTorsionThreeFormEquiv

open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem inverse_mul_coframe_coordinate
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : LorentzianIndex) :
    (∑ internal : LorentzianIndex,
      (coframe⁻¹) first internal * coframe internal second) =
      if first = second then 1 else 0 := by
  have inverseLaw := congrArg (fun matrix => matrix first second)
    (Matrix.nonsing_inv_mul coframe
      (isUnit_iff_ne_zero.mpr nondegenerate))
  simpa [Matrix.mul_apply, Matrix.one_apply] using inverseLaw

private theorem coframe_mul_inverse_coordinate
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : LorentzianIndex) :
    (∑ direction : LorentzianIndex,
      (coframe⁻¹) direction second * coframe first direction) =
      if first = second then 1 else 0 := by
  have inverseLaw := congrArg (fun matrix => matrix first second)
    (Matrix.mul_nonsing_inv coframe
      (isUnit_iff_ne_zero.mpr nondegenerate))
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using inverseLaw

/-- Coframe trace of a typed torsion two-form. -/
def cartanTorsionCoframeTrace
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm)
    (direction : LorentzianIndex) : ℝ :=
  ∑ internal : LorentzianIndex,
    ∑ spacetime : LorentzianIndex,
      (coframe⁻¹) spacetime internal *
        rawPointwiseCartanTorsion torsion spacetime direction internal

/-- Contract the undualized response once with the inverse coframe. -/
def cartanThreeFormFirstContraction
    (coframe : LorentzianCoframe)
    (form : PhysicalBivectorThreeForm)
    (internal first second : LorentzianIndex) : ℝ :=
  ∑ contractedInternal : LorentzianIndex,
    ∑ direction : LorentzianIndex,
      (coframe⁻¹) direction contractedInternal *
        orderedPhysicalBivectorThreeFormComponent form
          internal contractedInternal direction first second

/-- Contract the first response contraction once more. -/
def cartanThreeFormDoubleContraction
    (coframe : LorentzianCoframe)
    (form : PhysicalBivectorThreeForm)
    (direction : LorentzianIndex) : ℝ :=
  ∑ internal : LorentzianIndex,
    ∑ spacetime : LorentzianIndex,
      (coframe⁻¹) spacetime internal *
        cartanThreeFormFirstContraction coframe form
          internal spacetime direction

private theorem firstContraction_term_one
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion direction first internal *
            coframe contractedInternal second)) =
      -rawPointwiseCartanTorsion torsion first second internal := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ direction : LorentzianIndex,
        rawPointwiseCartanTorsion torsion direction first internal *
          (∑ contractedInternal : LorentzianIndex,
            (coframe⁻¹) direction contractedInternal *
              coframe contractedInternal second) := by
        apply Finset.sum_congr rfl
        intro direction _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro contractedInternal _
        ring
    _ = rawPointwiseCartanTorsion torsion second first internal := by
        simp_rw [inverse_mul_coframe_coordinate coframe nondegenerate]
        simp
    _ = -rawPointwiseCartanTorsion torsion first second internal := by
        exact rawPointwiseCartanTorsion_antisymm torsion second first internal

private theorem firstContraction_term_two
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion first second internal *
            coframe contractedInternal direction)) =
      4 * rawPointwiseCartanTorsion torsion first second internal := by
  calc
    _ = ∑ contractedInternal : LorentzianIndex,
        rawPointwiseCartanTorsion torsion first second internal *
          (∑ direction : LorentzianIndex,
            (coframe⁻¹) direction contractedInternal *
              coframe contractedInternal direction) := by
        apply Finset.sum_congr rfl
        intro contractedInternal _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro direction _
        ring
    _ = ∑ _ : LorentzianIndex,
        rawPointwiseCartanTorsion torsion first second internal := by
        apply Finset.sum_congr rfl
        intro contractedInternal _
        rw [coframe_mul_inverse_coordinate coframe nondegenerate
          contractedInternal contractedInternal]
        simp
    _ = 4 * rawPointwiseCartanTorsion torsion first second internal := by
        simp

private theorem firstContraction_term_three
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion second direction internal *
            coframe contractedInternal first)) =
      -rawPointwiseCartanTorsion torsion first second internal := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ direction : LorentzianIndex,
        rawPointwiseCartanTorsion torsion second direction internal *
          (∑ contractedInternal : LorentzianIndex,
            (coframe⁻¹) direction contractedInternal *
              coframe contractedInternal first) := by
        apply Finset.sum_congr rfl
        intro direction _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro contractedInternal _
        ring
    _ = rawPointwiseCartanTorsion torsion second first internal := by
        simp_rw [inverse_mul_coframe_coordinate coframe nondegenerate]
        simp
    _ = -rawPointwiseCartanTorsion torsion first second internal := by
        exact rawPointwiseCartanTorsion_antisymm torsion second first internal

private theorem firstContraction_term_four
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion direction first
              contractedInternal * coframe internal second)) =
      cartanTorsionCoframeTrace coframe torsion first *
        coframe internal second := by
  unfold cartanTorsionCoframeTrace
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro contractedInternal _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro direction _
  ring

private theorem firstContraction_term_five
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion first second
              contractedInternal * coframe internal direction)) =
      rawPointwiseCartanTorsion torsion first second internal := by
  calc
    _ = ∑ contractedInternal : LorentzianIndex,
        rawPointwiseCartanTorsion torsion first second contractedInternal *
          (∑ direction : LorentzianIndex,
            (coframe⁻¹) direction contractedInternal *
              coframe internal direction) := by
        apply Finset.sum_congr rfl
        intro contractedInternal _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro direction _
        ring
    _ = _ := by
        simp_rw [coframe_mul_inverse_coordinate coframe nondegenerate]
        simp

private theorem firstContraction_term_six
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    (∑ contractedInternal : LorentzianIndex,
      ∑ direction : LorentzianIndex,
        (coframe⁻¹) direction contractedInternal *
          (rawPointwiseCartanTorsion torsion second direction
              contractedInternal * coframe internal first)) =
      -cartanTorsionCoframeTrace coframe torsion second *
        coframe internal first := by
  simp_rw [rawPointwiseCartanTorsion_antisymm torsion second]
  calc
    _ = ∑ contractedInternal : LorentzianIndex,
        -(∑ direction : LorentzianIndex,
          (coframe⁻¹) direction contractedInternal *
            (rawPointwiseCartanTorsion torsion direction second
              contractedInternal * coframe internal first)) := by
        apply Finset.sum_congr rfl
        intro contractedInternal _
        calc
          _ = ∑ direction : LorentzianIndex,
              -((coframe⁻¹) direction contractedInternal *
                (rawPointwiseCartanTorsion torsion direction second
                  contractedInternal * coframe internal first)) := by
                apply Finset.sum_congr rfl
                intro direction _
                ring
          _ = _ := by rw [Finset.sum_neg_distrib]
    _ = -(∑ contractedInternal : LorentzianIndex,
        ∑ direction : LorentzianIndex,
          (coframe⁻¹) direction contractedInternal *
            (rawPointwiseCartanTorsion torsion direction second
              contractedInternal * coframe internal first)) := by
        rw [Finset.sum_neg_distrib]
    _ = -(cartanTorsionCoframeTrace coframe torsion second *
        coframe internal first) := by
        rw [firstContraction_term_four]
    _ = -cartanTorsionCoframeTrace coframe torsion second *
        coframe internal first := by ring

/-- First contraction of the actual undualized response. -/
theorem cartanThreeFormFirstContraction_wedge
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    cartanThreeFormFirstContraction coframe
        (cartanTorsionCoframeWedgeThreeForm coframe torsion)
        internal first second =
      rawPointwiseCartanTorsion torsion first second internal -
        cartanTorsionCoframeTrace coframe torsion first *
          coframe internal second +
        cartanTorsionCoframeTrace coframe torsion second *
          coframe internal first := by
  unfold cartanThreeFormFirstContraction
  simp_rw [ordered_cartanTorsionCoframeWedgeThreeForm]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [firstContraction_term_one coframe nondegenerate,
    firstContraction_term_two coframe nondegenerate,
    firstContraction_term_three coframe nondegenerate,
    firstContraction_term_four,
    firstContraction_term_five coframe nondegenerate,
    firstContraction_term_six]
  ring

private theorem inverseCoframe_vector_contraction
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (vector : LorentzianIndex → ℝ)
    (direction : LorentzianIndex) :
    (∑ internal : LorentzianIndex,
      ∑ spacetime : LorentzianIndex,
        (coframe⁻¹) spacetime internal *
          (vector spacetime * coframe internal direction)) =
      vector direction := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ spacetime : LorentzianIndex,
        vector spacetime *
          (∑ internal : LorentzianIndex,
            (coframe⁻¹) spacetime internal *
              coframe internal direction) := by
        apply Finset.sum_congr rfl
        intro spacetime _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro internal _
        ring
    _ = _ := by
        simp_rw [inverse_mul_coframe_coordinate coframe nondegenerate]
        simp

private theorem coframeInverseTrace_smul
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (scalar : ℝ) :
    (∑ internal : LorentzianIndex,
      ∑ spacetime : LorentzianIndex,
        (coframe⁻¹) spacetime internal *
          (scalar * coframe internal spacetime)) =
      4 * scalar := by
  calc
    _ = ∑ internal : LorentzianIndex,
        scalar *
          (∑ spacetime : LorentzianIndex,
            (coframe⁻¹) spacetime internal *
              coframe internal spacetime) := by
        apply Finset.sum_congr rfl
        intro internal _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro spacetime _
        ring
    _ = ∑ _ : LorentzianIndex, scalar := by
        apply Finset.sum_congr rfl
        intro internal _
        rw [coframe_mul_inverse_coordinate coframe nondegenerate
          internal internal]
        simp
    _ = 4 * scalar := by simp

/-- The double contraction is exactly four times the coframe trace.  This
is the dimensional identity that fixes the inverse coefficient `1/4`. -/
theorem cartanThreeFormDoubleContraction_wedge
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm)
    (direction : LorentzianIndex) :
    cartanThreeFormDoubleContraction coframe
        (cartanTorsionCoframeWedgeThreeForm coframe torsion)
        direction =
      4 * cartanTorsionCoframeTrace coframe torsion direction := by
  unfold cartanThreeFormDoubleContraction
  simp_rw [cartanThreeFormFirstContraction_wedge
    coframe nondegenerate torsion]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have firstTerm :
      (∑ internal : LorentzianIndex,
        ∑ spacetime : LorentzianIndex,
          (coframe⁻¹) spacetime internal *
            rawPointwiseCartanTorsion torsion spacetime direction internal) =
        cartanTorsionCoframeTrace coframe torsion direction := by
    rfl
  rw [firstTerm,
    inverseCoframe_vector_contraction coframe nondegenerate
      (cartanTorsionCoframeTrace coframe torsion) direction,
    coframeInverseTrace_smul coframe nondegenerate
      (cartanTorsionCoframeTrace coframe torsion direction)]
  ring

/-- Explicit inverse of the undualized `T wedge e` response. -/
def cartanTorsionOfUndualThreeForm
    (coframe : LorentzianCoframe)
    (form : PhysicalBivectorThreeForm) :
    PointwiseCartanTorsionTwoForm :=
  ⟨fun pair internal =>
    cartanThreeFormFirstContraction coframe form internal
        (pairFirst pair) (pairSecond pair) +
      (1 / 4 : ℝ) *
        (cartanThreeFormDoubleContraction coframe form (pairFirst pair) *
            coframe internal (pairSecond pair) -
          cartanThreeFormDoubleContraction coframe form (pairSecond pair) *
            coframe internal (pairFirst pair))⟩

/-- Explicit inverse of the action-facing `star_I (T wedge e)` response. -/
def cartanTorsionOfThreeForm
    (coframe : LorentzianCoframe)
    (response : PhysicalBivectorThreeForm) :
    PointwiseCartanTorsionTwoForm :=
  cartanTorsionOfUndualThreeForm coframe
    (internalBivectorUndualThreeForm response)

theorem cartanTorsionOfUndualThreeForm_leftInverse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionOfUndualThreeForm coframe
        (cartanTorsionCoframeWedgeThreeForm coframe torsion) =
      torsion := by
  ext pair internal
  simp only [cartanTorsionOfUndualThreeForm]
  rw [cartanThreeFormFirstContraction_wedge coframe nondegenerate,
    cartanThreeFormDoubleContraction_wedge coframe nondegenerate,
    cartanThreeFormDoubleContraction_wedge coframe nondegenerate]
  rw [rawPointwiseCartanTorsion_canonical]
  ring

theorem cartanTorsionOfThreeForm_leftInverse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionOfThreeForm coframe
        (cartanTorsionThreeForm coframe torsion) = torsion := by
  unfold cartanTorsionOfThreeForm cartanTorsionThreeForm
  rw [internalBivectorUndualThreeForm_dual]
  exact cartanTorsionOfUndualThreeForm_leftInverse
    coframe nondegenerate torsion

theorem cartanTorsionThreeForm_add
    (coframe : LorentzianCoframe)
    (first second : PointwiseCartanTorsionTwoForm) :
    cartanTorsionThreeForm coframe (first + second) =
      cartanTorsionThreeForm coframe first +
        cartanTorsionThreeForm coframe second := by
  funext internalPair triple
  fin_cases internalPair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm,
      cartanTorsionCoframeWedgeThreeForm,
      torsionCoframeWedgeThreeForm,
      internalBivectorDualThreeForm,
      rawPointwiseCartanTorsion,
      orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_six] <;>
    ring

theorem cartanTorsionThreeForm_smul
    (coframe : LorentzianCoframe) (scalar : ℝ)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionThreeForm coframe (scalar • torsion) =
      scalar • cartanTorsionThreeForm coframe torsion := by
  funext internalPair triple
  fin_cases internalPair <;> fin_cases triple <;>
    simp [cartanTorsionThreeForm,
      cartanTorsionCoframeWedgeThreeForm,
      torsionCoframeWedgeThreeForm,
      internalBivectorDualThreeForm,
      rawPointwiseCartanTorsion,
      orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_six] <;>
    ring

def cartanTorsionThreeFormLinearMap
    (coframe : LorentzianCoframe) :
    PointwiseCartanTorsionTwoForm →ₗ[ℝ] PhysicalBivectorThreeForm where
  toFun := cartanTorsionThreeForm coframe
  map_add' := cartanTorsionThreeForm_add coframe
  map_smul' := cartanTorsionThreeForm_smul coframe

private def torsionThreeFormCoordinateLinearEquiv :
    PointwiseCartanTorsionTwoForm ≃ₗ[ℝ] PhysicalBivectorThreeForm where
  toFun := PointwiseCartanTorsionTwoForm.component
  invFun := PointwiseCartanTorsionTwoForm.mk
  left_inv torsion := by cases torsion; rfl
  right_inv _ := rfl
  map_add' := by
    intro first second
    funext pair internal
    rfl
  map_smul' := by
    intro scalar torsion
    funext pair internal
    rfl

local instance cartanTorsionModuleFinite :
    Module.Finite ℝ PointwiseCartanTorsionTwoForm :=
  FiniteDimensional.of_injective
    torsionThreeFormCoordinateLinearEquiv.toLinearMap
    torsionThreeFormCoordinateLinearEquiv.injective

theorem cartanTorsionThreeForm_injective
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective (cartanTorsionThreeForm coframe) := by
  intro first second equality
  have inverseEquality :=
    congrArg (cartanTorsionOfThreeForm coframe) equality
  simpa only [cartanTorsionOfThreeForm_leftInverse coframe nondegenerate]
    using inverseEquality

theorem cartanTorsionThreeForm_surjective
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Surjective (cartanTorsionThreeForm coframe) := by
  have sameDimension :
      Module.finrank ℝ PointwiseCartanTorsionTwoForm =
        Module.finrank ℝ PhysicalBivectorThreeForm :=
    torsionThreeFormCoordinateLinearEquiv.finrank_eq
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      sameDimension
      (f := cartanTorsionThreeFormLinearMap coframe)).mp
      (cartanTorsionThreeForm_injective coframe nondegenerate)

theorem cartanTorsionOfThreeForm_rightInverse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (response : PhysicalBivectorThreeForm) :
    cartanTorsionThreeForm coframe
        (cartanTorsionOfThreeForm coframe response) = response := by
  rcases cartanTorsionThreeForm_surjective coframe nondegenerate response with
    ⟨torsion, rfl⟩
  rw [cartanTorsionOfThreeForm_leftInverse coframe nondegenerate]

/-- The no-free-parameter linear equivalence between typed torsion and the
actual KIN-1 response at a nondegenerate coframe. -/
def cartanTorsionThreeFormLinearEquiv
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    PointwiseCartanTorsionTwoForm ≃ₗ[ℝ] PhysicalBivectorThreeForm where
  toFun := cartanTorsionThreeForm coframe
  invFun := cartanTorsionOfThreeForm coframe
  left_inv := cartanTorsionOfThreeForm_leftInverse coframe nondegenerate
  right_inv := cartanTorsionOfThreeForm_rightInverse coframe nondegenerate
  map_add' := cartanTorsionThreeForm_add coframe
  map_smul' := cartanTorsionThreeForm_smul coframe

@[simp] theorem cartanTorsionThreeFormLinearEquiv_apply
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionThreeFormLinearEquiv coframe nondegenerate torsion =
      cartanTorsionThreeForm coframe torsion :=
  rfl

@[simp] theorem cartanTorsionThreeFormLinearEquiv_symm_apply
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (response : PhysicalBivectorThreeForm) :
    (cartanTorsionThreeFormLinearEquiv coframe nondegenerate).symm response =
      cartanTorsionOfThreeForm coframe response :=
  rfl

@[simp] theorem cartanTorsionThreeForm_eq_zero_iff
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionThreeForm coframe torsion = 0 ↔ torsion = 0 := by
  exact
    (cartanTorsionThreeFormLinearEquiv coframe nondegenerate).map_eq_zero_iff

end

end
  SaturationMonoid.PhysicsCore.StageNineCartanTorsionThreeFormEquiv
