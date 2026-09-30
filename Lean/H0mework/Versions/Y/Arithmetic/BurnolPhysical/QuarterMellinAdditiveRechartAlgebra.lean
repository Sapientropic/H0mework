import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartNorm

/-!
# Linear isometry of the quarter-Mellin additive rechart

The source-exact rechart is linear, factors through the actual quarter-feature
range, and becomes an isometry after multiplication by two.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem quarterMellinAdditiveEvenRechart_add {z : ℂ}
    (left right : QuarterMellinL2Test z) :
    quarterMellinAdditiveEvenRechart (left + right) =
      quarterMellinAdditiveEvenRechart left +
        quarterMellinAdditiveEvenRechart right := by
  apply Lp.ext
  filter_upwards [
    quarterMellinAdditiveEvenRechart_coeFn (left + right),
    quarterMellinAdditiveEvenRechart_coeFn left,
    quarterMellinAdditiveEvenRechart_coeFn right,
    Lp.coeFn_add (quarterMellinAdditiveEvenRechart left)
      (quarterMellinAdditiveEvenRechart right)]
      with x sumRead leftRead rightRead targetAdd
  rw [targetAdd, sumRead]
  change quarterMellinAdditiveEvenRechartRaw (left + right) x =
    (quarterMellinAdditiveEvenRechart left : ℝ → ℂ) x +
      (quarterMellinAdditiveEvenRechart right : ℝ → ℂ) x
  rw [leftRead, rightRead]
  by_cases hx : x = 0
  · simp [hx, quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension]
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension,
      hx2]
    ring

theorem quarterMellinAdditiveEvenRechart_smul {z : ℂ}
    (coefficient : ℂ) (value : QuarterMellinL2Test z) :
    quarterMellinAdditiveEvenRechart (coefficient • value) =
      coefficient • quarterMellinAdditiveEvenRechart value := by
  apply Lp.ext
  filter_upwards [
    quarterMellinAdditiveEvenRechart_coeFn (coefficient • value),
    quarterMellinAdditiveEvenRechart_coeFn value,
    Lp.coeFn_smul coefficient (quarterMellinAdditiveEvenRechart value)]
      with x scaledRead valueRead targetSmul
  rw [targetSmul, scaledRead]
  change quarterMellinAdditiveEvenRechartRaw (coefficient • value) x =
    coefficient • (quarterMellinAdditiveEvenRechart value : ℝ → ℂ) x
  rw [valueRead]
  by_cases hx : x = 0
  · simp [hx, quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension]
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension,
      hx2]
    ring

def quarterMellinAdditiveEvenRechartLinear (z : ℂ) :
    QuarterMellinL2Test z →ₗ[ℂ] BurnolL2 where
  toFun := quarterMellinAdditiveEvenRechart
  map_add' := quarterMellinAdditiveEvenRechart_add
  map_smul' := quarterMellinAdditiveEvenRechart_smul

@[simp] theorem quarterMellinAdditiveEvenRechartLinear_apply
    {z : ℂ} (value : QuarterMellinL2Test z) :
    quarterMellinAdditiveEvenRechartLinear z value =
      quarterMellinAdditiveEvenRechart value := rfl

theorem quarterMellinAdditiveEvenRechart_eq_of_feature_eq
    {z : ℂ} {left right : QuarterMellinL2Test z}
    (featureEq : quarterMellinL2Feature z left =
      quarterMellinL2Feature z right) :
    quarterMellinAdditiveEvenRechart left =
      quarterMellinAdditiveEvenRechart right := by
  have featureSub : quarterMellinL2Feature z (left - right) = 0 := by
    rw [map_sub, featureEq, sub_self]
  have rechartSubNorm :=
    quarterMellinAdditiveEvenRechart_norm (left - right)
  rw [featureSub, norm_zero, mul_zero] at rechartSubNorm
  have rechartSub : quarterMellinAdditiveEvenRechart (left - right) = 0 :=
    norm_eq_zero.mp rechartSubNorm
  change quarterMellinAdditiveEvenRechartLinear z (left - right) = 0
    at rechartSub
  rw [map_sub] at rechartSub
  exact sub_eq_zero.mp rechartSub

/-- The rechart depends on the underlying positive function, not on which
Mellin-convergence coordinate supplies its lawful test receipt. -/
theorem quarterMellinAdditiveEvenRechart_eq_of_source_eq
    {z w : ℂ} {left : QuarterMellinL2Test z}
    {right : QuarterMellinL2Test w} (sourceEq : left.1 = right.1) :
    quarterMellinAdditiveEvenRechart left =
      quarterMellinAdditiveEvenRechart right := by
  apply Lp.ext
  filter_upwards [quarterMellinAdditiveEvenRechart_coeFn left,
    quarterMellinAdditiveEvenRechart_coeFn right] with x leftRead rightRead
  rw [leftRead, rightRead]
  unfold quarterMellinAdditiveEvenRechartRaw
    quarterMellinAdditivePositiveRechartRaw
  rw [sourceEq]

private def quarterMellinFeatureRangeSource (z : ℂ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    QuarterMellinL2Test z :=
  Classical.choose value.property

private theorem quarterMellinFeatureRangeSource_spec (z : ℂ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    quarterMellinL2Feature z (quarterMellinFeatureRangeSource z value) =
      value.1 :=
  Classical.choose_spec value.property

private def quarterMellinFeatureRangeEvenAdditiveValue (z : ℂ)
    (value : LinearMap.range (quarterMellinL2Feature z)) : BurnolL2 :=
  (2 : ℂ) • quarterMellinAdditiveEvenRechart
    (quarterMellinFeatureRangeSource z value)

private theorem quarterMellinFeatureRangeEvenAdditiveValue_add (z : ℂ)
    (left right : LinearMap.range (quarterMellinL2Feature z)) :
    quarterMellinFeatureRangeEvenAdditiveValue z (left + right) =
      quarterMellinFeatureRangeEvenAdditiveValue z left +
        quarterMellinFeatureRangeEvenAdditiveValue z right := by
  have sourceEq :
      quarterMellinAdditiveEvenRechart
          (quarterMellinFeatureRangeSource z (left + right)) =
        quarterMellinAdditiveEvenRechart
          (quarterMellinFeatureRangeSource z left +
            quarterMellinFeatureRangeSource z right) := by
    apply quarterMellinAdditiveEvenRechart_eq_of_feature_eq
    rw [map_add, quarterMellinFeatureRangeSource_spec,
      quarterMellinFeatureRangeSource_spec,
      quarterMellinFeatureRangeSource_spec]
    rfl
  unfold quarterMellinFeatureRangeEvenAdditiveValue
  rw [sourceEq, quarterMellinAdditiveEvenRechart_add, smul_add]

private theorem quarterMellinFeatureRangeEvenAdditiveValue_smul (z : ℂ)
    (coefficient : ℂ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    quarterMellinFeatureRangeEvenAdditiveValue z (coefficient • value) =
      coefficient • quarterMellinFeatureRangeEvenAdditiveValue z value := by
  have sourceEq :
      quarterMellinAdditiveEvenRechart
          (quarterMellinFeatureRangeSource z (coefficient • value)) =
        quarterMellinAdditiveEvenRechart
          (coefficient • quarterMellinFeatureRangeSource z value) := by
    apply quarterMellinAdditiveEvenRechart_eq_of_feature_eq
    rw [map_smul, quarterMellinFeatureRangeSource_spec,
      quarterMellinFeatureRangeSource_spec]
    rfl
  unfold quarterMellinFeatureRangeEvenAdditiveValue
  rw [sourceEq, quarterMellinAdditiveEvenRechart_smul]
  module

private theorem quarterMellinFeatureRangeEvenAdditiveValue_norm (z : ℂ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    ‖quarterMellinFeatureRangeEvenAdditiveValue z value‖ = ‖value‖ := by
  unfold quarterMellinFeatureRangeEvenAdditiveValue
  rw [norm_smul, quarterMellinAdditiveEvenRechart_norm,
    quarterMellinFeatureRangeSource_spec]
  change ‖(2 : ℂ)‖ *
      ((1 / 2 : ℝ) * ‖(value : PositiveMellinQuarterEnergy)‖) =
    ‖(value : PositiveMellinQuarterEnergy)‖
  norm_num
  ring

/-- Twice the reciprocal-square additive rechart is the canonical linear
isometry from the actual quarter-feature range into additive Burnol L². -/
def quarterMellinFeatureRangeEvenAdditiveIsometry (z : ℂ) :
    LinearMap.range (quarterMellinL2Feature z) →ₗᵢ[ℂ] BurnolL2 where
  toLinearMap :=
    { toFun := quarterMellinFeatureRangeEvenAdditiveValue z
      map_add' := quarterMellinFeatureRangeEvenAdditiveValue_add z
      map_smul' := quarterMellinFeatureRangeEvenAdditiveValue_smul z }
  norm_map' := quarterMellinFeatureRangeEvenAdditiveValue_norm z

theorem quarterMellinFeatureRangeEvenAdditiveIsometry_source
    {z : ℂ} (value : QuarterMellinL2Test z) :
    quarterMellinFeatureRangeEvenAdditiveIsometry z
        ((quarterMellinL2Feature z).rangeRestrict value) =
      (2 : ℂ) • quarterMellinAdditiveEvenRechart value := by
  unfold quarterMellinFeatureRangeEvenAdditiveIsometry
    quarterMellinFeatureRangeEvenAdditiveValue
  change (2 : ℂ) • quarterMellinAdditiveEvenRechart
      (quarterMellinFeatureRangeSource z
        ((quarterMellinL2Feature z).rangeRestrict value)) =
    (2 : ℂ) • quarterMellinAdditiveEvenRechart value
  apply congrArg ((2 : ℂ) • ·)
  apply quarterMellinAdditiveEvenRechart_eq_of_feature_eq
  rw [quarterMellinFeatureRangeSource_spec]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
