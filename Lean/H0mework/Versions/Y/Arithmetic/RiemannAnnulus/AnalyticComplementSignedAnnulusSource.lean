import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.AnalyticComplementNormalizedSource

/-!
# Source-generated signed stable annulus

The coordinate-normalized source is supported in `1 < |x| < 3`.  Its actual
quarter-dilation therefore remains in the fixed Burnol annulus whenever
`sqrt (exp shift)` lies in `[3/4, 4]`, including the previously unavailable
negative interval down to `-log (16/9)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped SchwartzMap

noncomputable section

/-- A genuinely signed source segment.  Its lower endpoint is dictated by
the outer support bound `3`, while its upper endpoint is dictated by the
protected inner gap `1/4`. -/
structure BurnolCompactAnnulusSignedDilationSegment
    (source : burnolCompactAnnulusSource) where
  sourceAt : (shift : ℝ) →
    -Real.log (16 / 9 : ℝ) ≤ shift → shift ≤ Real.log 16 →
      burnolCompactAnnulusSource
  sourceAt_coe : ∀ (shift : ℝ)
      (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
      (upper : shift ≤ Real.log 16),
    (sourceAt shift lower upper).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift) source.1

private theorem signedAnnulus_sqrt_exp_bounds
    {shift : ℝ}
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    (3 / 4 : ℝ) ≤ Real.sqrt (Real.exp shift) ∧
      Real.sqrt (Real.exp shift) ≤ 4 := by
  have leftEndpointExp :
      Real.exp (-Real.log (16 / 9 : ℝ)) = (9 / 16 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16 / 9)]
    norm_num
  have expLower : (9 / 16 : ℝ) ≤ Real.exp shift := by
    calc
      (9 / 16 : ℝ) = Real.exp (-Real.log (16 / 9 : ℝ)) :=
        leftEndpointExp.symm
      _ ≤ Real.exp shift := Real.exp_le_exp.mpr lower
  have expUpper : Real.exp shift ≤ 16 := by
    calc
      Real.exp shift ≤ Real.exp (Real.log 16) :=
        Real.exp_le_exp.mpr upper
      _ = 16 := Real.exp_log (by norm_num)
  have square := Real.sq_sqrt (Real.exp_pos shift).le
  have sqrtNonnegative := Real.sqrt_nonneg (Real.exp shift)
  constructor <;> nlinarith

/-- Actual signed dilation of the coordinate-matched compact source.  The support bounds generate admission on both sides of zero. -/
def burnolCoordinateMatchedSignedDilationSource
    (coordinate : ℂ) (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  ⟨quarterMuntzSchwartzDilationAction
      (Real.exp shift) (Real.exp_pos shift)
      (burnolCoordinateMatchedAnnulusSource coordinate).1,
    by
      obtain ⟨sqrtLower, sqrtUpper⟩ :=
        signedAnnulus_sqrt_exp_bounds lower upper
      refine ⟨?_, ?_, ?_⟩
      · intro x
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoordinateMatchedAnnulusSchwartz coordinate
              (Real.sqrt (Real.exp shift) * -x) =
          positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoordinateMatchedAnnulusSchwartz coordinate
              (Real.sqrt (Real.exp shift) * x)
        rw [show Real.sqrt (Real.exp shift) * -x =
            -(Real.sqrt (Real.exp shift) * x) by ring]
        simp [burnolCoordinateMatchedEvenRaw, add_comm]
      · intro x inside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoordinateMatchedAnnulusSchwartz coordinate
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoordinateMatchedAnnulusSchwartz_zero_of_abs_le_one]
        · simp
        · rw [abs_mul, abs_of_nonneg
              (Real.sqrt_nonneg (Real.exp shift))]
          nlinarith [abs_nonneg x]
      · intro x outside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoordinateMatchedAnnulusSchwartz coordinate
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoordinateMatchedAnnulusSchwartz_zero_of_three_le_abs]
        · simp
        · rw [abs_mul, abs_of_nonneg
              (Real.sqrt_nonneg (Real.exp shift))]
          nlinarith [abs_nonneg x]⟩

theorem burnolCoordinateMatchedSignedDilationSource_coe
    (coordinate : ℂ) (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    (burnolCoordinateMatchedSignedDilationSource
        coordinate shift lower upper).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        (burnolCoordinateMatchedAnnulusSource coordinate).1 := by
  rfl

/-- The normalized source keeps the same signed dilation occurrence. -/
def burnolCoordinateNormalizedSignedDilationSource
    (coordinate : ℂ) (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  burnolCoordinateMatchedNormalizer coordinate •
    burnolCoordinateMatchedSignedDilationSource
      coordinate shift lower upper

theorem burnolCoordinateNormalizedSignedDilationSource_coe
    (coordinate : ℂ) (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    (burnolCoordinateNormalizedSignedDilationSource
        coordinate shift lower upper).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        (burnolCoordinateNormalizedAnnulusSource coordinate).1 := by
  change burnolCoordinateMatchedNormalizer coordinate •
      (burnolCoordinateMatchedSignedDilationSource
        coordinate shift lower upper).1 = _
  rw [burnolCoordinateMatchedSignedDilationSource_coe,
    show (burnolCoordinateNormalizedAnnulusSource coordinate).1 =
      burnolCoordinateMatchedNormalizer coordinate •
        (burnolCoordinateMatchedAnnulusSource coordinate).1 by rfl,
    map_smul]

/-- Signed sourceAt specialized to the exact analytic-complement occurrence. -/
def burnolAnalyticComplementSignedDilationSource
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  burnolCoordinateNormalizedSignedDilationSource
    (1 - observation.coordinate) shift lower upper

theorem burnolAnalyticComplementSignedDilationSource_coe
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    (burnolAnalyticComplementSignedDilationSource
        observation shift lower upper).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        (burnolAnalyticComplementNormalizedSource observation).1 := by
  exact burnolCoordinateNormalizedSignedDilationSource_coe
    (1 - observation.coordinate) shift lower upper

/-- The same analytic-complement source owns the whole signed sourceAt
inventory, including negative shifts. -/
def burnolAnalyticComplementSignedDilationSegment
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    BurnolCompactAnnulusSignedDilationSegment
      (burnolAnalyticComplementNormalizedSource observation) where
  sourceAt := burnolAnalyticComplementSignedDilationSource observation
  sourceAt_coe := burnolAnalyticComplementSignedDilationSource_coe observation

/-- Every point of the signed segment remains an actual compact co-Poisson
source.  At the selected zero its quarter-Mellin relation is still
annihilated, while its projected additive state lands in the existing
physical closed range. -/
theorem burnolAnalyticComplementSignedDilationSource_physicalLanding
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ)
    (lower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (upper : shift ≤ Real.log 16) :
    let z := observation.coordinate / 2
    let positive :=
      selectedCoPoissonMuntzParameter_re_pos observation nontrivial
    let belowHalf :=
      selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial
    let sourceAt :=
      (burnolAnalyticComplementSignedDilationSegment observation).sourceAt
        shift lower upper
    let relation := coPoissonQuarterMellinConvergentMap
      z positive belowHalf sourceAt.1
    quarterMellinL2Functional z relation = 0 ∧
      quarterMellinAdditiveProjectedPhysicalState relation =
        burnolCompactAdditivePhysicalState sourceAt ∧
      quarterMellinAdditiveProjectedPhysicalState relation ∈
        burnolCompactCoPoissonClosedRange := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact LinearMap.congr_fun
      (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
        observation nontrivial)
      (burnolAnalyticComplementSignedDilationSource
        observation shift lower upper).1
  · exact compactQuarterMellinAdditiveProjectedPhysicalState_eq
      (observation.coordinate / 2)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (burnolAnalyticComplementSignedDilationSource
        observation shift lower upper)
  · exact compactQuarterMellinAdditiveProjectedPhysicalState_mem_closedRange
      (observation.coordinate / 2)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      (burnolAnalyticComplementSignedDilationSource
        observation shift lower upper)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
