import H0mework.Versions.R7e4da746.Arithmetic.TruncatedFourier.DilationAction
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.DirectRightResolvent

set_option autoImplicit false
set_option maxHeartbeats 30000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

/-- The existing two constant-gap conditions with independent position and
Fourier radii. -/
def burnolRectangularBurnolFace (position frequency : ℝ) :
    Submodule ℂ BurnolL2 :=
  locallyConstantFace position ⊓
    (locallyConstantFace frequency).comap fourierL2.toLinearMap

def burnolEvenRectangularBurnolFace (position frequency : ℝ) :
    Submodule ℂ BurnolL2 :=
  burnolRectangularBurnolFace position frequency ⊓ evenL2ClosedFace.toSubmodule

/-- The closed even two-window face on the original full-line L² carrier. -/
def burnolEvenRectangularBurnolClosedFace (position frequency : ℝ) :
    ClosedSubmodule ℂ BurnolL2 where
  toSubmodule := burnolEvenRectangularBurnolFace position frequency
  isClosed' :=
    ((locallyConstantFace_isClosed position).inter
      ((locallyConstantFace_isClosed frequency).preimage fourierL2.continuous)).inter
      evenL2ClosedFace.isClosed

theorem mem_burnolEvenRectangularBurnolFace_iff
    {position frequency : ℝ} {value : BurnolL2} :
    value ∈ burnolEvenRectangularBurnolFace position frequency ↔
      ((value ∈ locallyConstantFace position) ∧
        (fourierL2.toLinearMap value ∈ locallyConstantFace frequency)) ∧
        value ∈ evenL2ClosedFace :=
  Iff.rfl

theorem burnolEvenRectangularBurnolClosedFace_diagonal (radius : ℝ) :
    burnolEvenRectangularBurnolClosedFace radius radius =
      evenBurnolClosedFace radius := by
  ext value
  rfl

private theorem burnol_dilation_window_membership (radius h x : ℝ) :
    Real.exp h * x ∈ symmetricInterval radius ↔
      x ∈ symmetricInterval (radius * Real.exp (-h)) := by
  simp only [symmetricInterval, Set.mem_Icc, ← abs_le, abs_mul,
    abs_of_pos (Real.exp_pos h)]
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using
    (le_div_iff₀ (Real.exp_pos h) :
      |x| ≤ radius / Real.exp h ↔ |x| * Real.exp h ≤ radius).symm

/-- Exact moving-radius covariance of one actual constant-gap condition. -/
theorem burnolMultiplicativeDilation_mem_locallyConstantFace_scaled
    {radius : ℝ} (h : ℝ) {value : BurnolL2}
    (membership : value ∈ locallyConstantFace radius) :
    burnolMultiplicativeDilation h value ∈
      locallyConstantFace (radius * Real.exp (-h)) := by
  rw [mem_locallyConstantFace_iff_exists] at membership ⊢
  obtain ⟨coefficient, coefficientRead⟩ := membership
  refine ⟨(Real.exp (h / 2) : ℂ) * coefficient, ?_⟩
  apply Lp.ext
  have scaleQmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  have sourceRestricted :
      value =ᵐ[volume.restrict (symmetricInterval radius)]
        fun _ : ℝ => coefficient := by
    have restrictionRead := LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval radius) value
    have constantRead := intervalConstant_coeFn radius
    have smulRead := Lp.coeFn_smul coefficient (intervalConstant radius)
    filter_upwards [restrictionRead, constantRead, smulRead]
      with x restrictionAt constantAt smulAt
    calc
      value x = restrictToInterval radius value x := restrictionAt.symm
      _ = (coefficient • intervalConstant radius) x := by rw [coefficientRead]
      _ = coefficient * intervalConstant radius x := smulAt
      _ = coefficient := by rw [constantAt, mul_one]
  have sourceGlobal : ∀ᵐ x ∂volume,
      x ∈ symmetricInterval radius → value x = coefficient :=
    (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
      sourceRestricted
  have sourceScaled : ∀ᵐ x ∂volume,
      Real.exp h * x ∈ symmetricInterval radius →
        value (Real.exp h * x) = coefficient := by
    filter_upwards [scaleQmp.ae sourceGlobal] with x sourceAt
    exact sourceAt
  let targetRadius := radius * Real.exp (-h)
  filter_upwards [
    Lp.coeFn_smul ((Real.exp (h / 2) : ℂ) * coefficient)
      (intervalConstant targetRadius),
    intervalConstant_coeFn targetRadius,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval targetRadius)
      (burnolMultiplicativeDilation h value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn h value),
    ae_restrict_of_ae sourceScaled,
    ae_restrict_mem (measurableSet_symmetricInterval targetRadius)]
      with x targetSmul constantAt restrictionAt dilationAt sourceAt inside
  have scaledInside : Real.exp h * x ∈ symmetricInterval radius :=
    (burnol_dilation_window_membership radius h x).mpr inside
  calc
    (((Real.exp (h / 2) : ℂ) * coefficient) •
        intervalConstant targetRadius :
        Lp ℂ 2 (volume.restrict (symmetricInterval targetRadius))) x =
      ((Real.exp (h / 2) : ℂ) * coefficient) *
        intervalConstant targetRadius x := targetSmul
    _ = (Real.exp (h / 2) : ℂ) * coefficient := by rw [constantAt, mul_one]
    _ = (Real.exp (h / 2) : ℂ) * value (Real.exp h * x) := by
      rw [sourceAt scaledInside]
    _ = burnolL2RawNormalizedDilation h value x := rfl
    _ = burnolMultiplicativeDilation h value x := dilationAt.symm
    _ = restrictToInterval targetRadius
        (burnolMultiplicativeDilation h value) x := restrictionAt.symm

/-- The moving local face is carried exactly, not merely included. -/
theorem burnolMultiplicativeDilation_mem_locallyConstantFace_scaled_iff
    {radius : ℝ} (h : ℝ) {value : BurnolL2} :
    burnolMultiplicativeDilation h value ∈
        locallyConstantFace (radius * Real.exp (-h)) ↔
      value ∈ locallyConstantFace radius := by
  constructor
  · intro target
    have back := burnolMultiplicativeDilation_mem_locallyConstantFace_scaled
      (radius := radius * Real.exp (-h)) (-h) target
    have radiusRead :
        (radius * Real.exp (-h)) * Real.exp (-(-h)) = radius := by
      rw [neg_neg, Real.exp_neg]
      field_simp
    rw [radiusRead] at back
    rw [burnolMultiplicativeDilation_neg_eq_symm h,
      (burnolMultiplicativeDilation h).symm_apply_apply] at back
    exact back
  · exact burnolMultiplicativeDilation_mem_locallyConstantFace_scaled h

private theorem burnolMultiplicativeDilation_mem_evenL2ClosedFace_iff
    (h : ℝ) {value : BurnolL2} :
    burnolMultiplicativeDilation h value ∈ evenL2ClosedFace ↔
      value ∈ evenL2ClosedFace := by
  constructor
  · intro target
    have back := burnolMultiplicativeDilation_mem_evenL2ClosedFace
      (-h) (burnolMultiplicativeDilation h value) target
    rw [burnolMultiplicativeDilation_neg_eq_symm h,
      (burnolMultiplicativeDilation h).symm_apply_apply] at back
    exact back
  · exact burnolMultiplicativeDilation_mem_evenL2ClosedFace h value

private theorem burnol_fourierLinearMap_burnolMultiplicativeDilation
    (h : ℝ) (value : BurnolL2) :
    fourierL2.toLinearMap (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation (-h) (fourierL2.toLinearMap value) := by
  exact fourierL2_burnolMultiplicativeDilation h value

private theorem burnolMultiplicativeDilation_mem_evenRectangularFace_scaled
    {position frequency : ℝ} (h : ℝ) {value : BurnolL2} :
    value ∈ burnolEvenRectangularBurnolFace position frequency →
      burnolMultiplicativeDilation h value ∈
        burnolEvenRectangularBurnolFace
          (position * Real.exp (-h)) (frequency * Real.exp h) := by
  intro source
  rw [mem_burnolEvenRectangularBurnolFace_iff] at source ⊢
  have sourcePosition : value ∈ locallyConstantFace position := source.1.1
  have sourceFourier : fourierL2.toLinearMap value ∈ locallyConstantFace frequency :=
    source.1.2
  have sourceEven : value ∈ evenL2ClosedFace := source.2
  refine ⟨⟨burnolMultiplicativeDilation_mem_locallyConstantFace_scaled h
    sourcePosition, ?_⟩,
    burnolMultiplicativeDilation_mem_evenL2ClosedFace h value sourceEven⟩
  rw [burnol_fourierLinearMap_burnolMultiplicativeDilation]
  simpa only [neg_neg] using
    (burnolMultiplicativeDilation_mem_locallyConstantFace_scaled
      (radius := frequency) (-h) sourceFourier)

private theorem burnolMultiplicativeDilation_reflects_evenRectangularFace_scaled
    {position frequency : ℝ} (h : ℝ) {value : BurnolL2} :
    burnolMultiplicativeDilation h value ∈
        burnolEvenRectangularBurnolFace
          (position * Real.exp (-h)) (frequency * Real.exp h) →
      value ∈ burnolEvenRectangularBurnolFace position frequency := by
  intro target
  rw [mem_burnolEvenRectangularBurnolFace_iff] at target ⊢
  have targetPosition : burnolMultiplicativeDilation h value ∈
      locallyConstantFace (position * Real.exp (-h)) := target.1.1
  have targetFourier : fourierL2.toLinearMap (burnolMultiplicativeDilation h value) ∈
      locallyConstantFace (frequency * Real.exp h) := target.1.2
  have targetEven : burnolMultiplicativeDilation h value ∈ evenL2ClosedFace := target.2
  have positionRead : value ∈ locallyConstantFace position :=
    (burnolMultiplicativeDilation_mem_locallyConstantFace_scaled_iff
      (radius := position) h).mp targetPosition
  have transformedFourier :
      burnolMultiplicativeDilation (-h) (fourierL2.toLinearMap value) ∈
      locallyConstantFace (frequency * Real.exp h) := by
    rw [← burnol_fourierLinearMap_burnolMultiplicativeDilation]
    exact targetFourier
  have frequencyRead : fourierL2.toLinearMap value ∈
      locallyConstantFace frequency := by
    apply (burnolMultiplicativeDilation_mem_locallyConstantFace_scaled_iff
      (radius := frequency) (-h)).mp
    simpa only [neg_neg] using transformedFourier
  exact ⟨⟨positionRead, frequencyRead⟩,
    (burnolMultiplicativeDilation_mem_evenL2ClosedFace_iff h).mp targetEven⟩

/-- The actual normalized dilation carries the full even two-window face
exactly to the contragrediently scaled position/Fourier windows. -/
theorem burnolMultiplicativeDilation_mem_evenRectangularFace_scaled_iff
    {position frequency : ℝ} (h : ℝ) {value : BurnolL2} :
    burnolMultiplicativeDilation h value ∈
        burnolEvenRectangularBurnolFace
          (position * Real.exp (-h)) (frequency * Real.exp h) ↔
      value ∈ burnolEvenRectangularBurnolFace position frequency :=
  ⟨burnolMultiplicativeDilation_reflects_evenRectangularFace_scaled h,
    burnolMultiplicativeDilation_mem_evenRectangularFace_scaled h⟩

theorem burnolEvenRectangularBurnolClosedFace_map_dilation
    (position frequency h : ℝ) :
    (burnolEvenRectangularBurnolFace position frequency).map
        (burnolMultiplicativeDilation h).toLinearEquiv.toLinearMap =
      burnolEvenRectangularBurnolFace
        (position * Real.exp (-h)) (frequency * Real.exp h) := by
  ext value
  rw [Submodule.mem_map_equiv]
  simpa using
    (burnolMultiplicativeDilation_mem_evenRectangularFace_scaled_iff
      (position := position) (frequency := frequency) h
      (value := (burnolMultiplicativeDilation h).symm value)).symm

local instance burnolEvenRectangularBurnolComplete
    (position frequency : ℝ) :
    CompleteSpace (burnolEvenRectangularBurnolFace position frequency) := by
  apply IsComplete.completeSpace_coe
  exact (burnolEvenRectangularBurnolClosedFace position frequency).isClosed.isComplete

/-- Genuine moving-face orthogonal-projection conjugacy.  Both projections are
generated from the existing closed submodules; no preservation premise enters. -/
theorem burnolEvenRectangularBurnolProjection_conjugacy
    (position frequency h : ℝ) (value : BurnolL2) :
    (burnolEvenRectangularBurnolFace
        (position * Real.exp (-h)) (frequency * Real.exp h)).starProjection
        value =
      burnolMultiplicativeDilation h
        ((burnolEvenRectangularBurnolFace position frequency).starProjection
          ((burnolMultiplicativeDilation h).symm value)) := by
  have generated := Submodule.starProjection_map_apply
    (burnolMultiplicativeDilation h)
    (burnolEvenRectangularBurnolFace position frequency) value
  simpa only [burnolEvenRectangularBurnolClosedFace_map_dilation] using generated


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
