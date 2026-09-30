import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.AnalyticComplementFinitePartRead

/-! # Analytic-complement exact-order division jet -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter Topology
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The resonance point for the analytic complement in quarter coordinates. -/
def burnolAnalyticComplementDivisionCenter
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) : ℂ :=
  (1 / 2 : ℂ) - observation.coordinate / 2

/-- The source-generated scalar remaining after `k` algebraic continuations
of the right-resolvent division.  Only stages `k ≤ ordρ` are consumed below. -/
def burnolAnalyticComplementDivisionJet
    (owner : GlobalGermOwner)
    (observation : GeneratedRiemannZeroObservationAt owner)
    (k : ℕ) (w : ℂ) : ℂ :=
  (-1 : ℂ) ^ k *
    (w - burnolAnalyticComplementDivisionCenter observation) ^
      (generatedRiemannXiZeroOrder owner observation.coordinate - k) *
    burnolAnalyticComplementQuarterQuotient owner observation w

/-- Stage zero is exactly the source Mellin transform wherever the source
factorization is available. -/
theorem burnolAnalyticComplementDivisionJet_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (w : ℂ)
    (valuePositive : 0 < (2 * w).re) (valueBelowOne : (2 * w).re < 1)
    (valueNeZero : 2 * w ≠ 0) (valueNeOne : 2 * w ≠ 1)
    (gammaNeZero : Gammaℝ (2 * w) ≠ 0) :
    burnolAnalyticComplementDivisionJet owner observation 0 w =
      mellin
        (positiveMellinExtension
          (coPoissonQuarterMellinMap
            (burnolAnalyticComplementNormalizedSource observation).1)) w := by
  rw [burnolAnalyticComplementQuarter_factorization observation w
    valuePositive valueBelowOne valueNeZero valueNeOne gammaNeZero]
  simp [burnolAnalyticComplementDivisionJet,
    burnolAnalyticComplementDivisionCenter]

/-- One source-generated right-resolvent scalar division advances the jet by
one stage while a positive zero-order factor remains. -/
theorem burnolAnalyticComplementDivisionJet_succ
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (w : ℂ)
    (nonresonant :
      w ≠ burnolAnalyticComplementDivisionCenter observation) :
    (-(1 / (observation.coordinate / 2 + w - (1 / 2 : ℂ)))) *
        burnolAnalyticComplementDivisionJet owner observation k w =
      burnolAnalyticComplementDivisionJet owner observation (k + 1) w := by
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  let difference := w - burnolAnalyticComplementDivisionCenter observation
  have differenceNe : difference ≠ 0 := sub_ne_zero.mpr nonresonant
  have denominator :
      observation.coordinate / 2 + w - (1 / 2 : ℂ) = difference := by
    dsimp only [difference, burnolAnalyticComplementDivisionCenter]
    ring
  have exponent : order - k = (order - (k + 1)) + 1 := by
    omega
  rw [denominator]
  unfold burnolAnalyticComplementDivisionJet
  change (-(1 / difference)) *
      ((-1 : ℂ) ^ k * difference ^ (order - k) *
        burnolAnalyticComplementQuarterQuotient owner observation w) =
    (-1 : ℂ) ^ (k + 1) * difference ^ (order - (k + 1)) *
      burnolAnalyticComplementQuarterQuotient owner observation w
  rw [exponent, pow_succ]
  field_simp [differenceNe]
  ring

/-- The analytic right-resolvent kernel realizes the preceding algebraic
stage law on its nonresonant half-plane. -/
theorem burnolAnalyticComplementDivisionJet_succ_eq_scalarKernel
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (w : ℂ)
    (decay :
      (((1 / 2 : ℂ) - observation.coordinate / 2 - w).re < 0))
    (nonresonant :
      w ≠ burnolAnalyticComplementDivisionCenter observation) :
    (-(∫ shift : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventWeight
            (observation.coordinate / 2) shift *
          quarterDilationCharacter w (Real.exp shift))) *
        burnolAnalyticComplementDivisionJet owner observation k w =
      burnolAnalyticComplementDivisionJet owner observation (k + 1) w := by
  rw [positiveMellinQuarterRightResolvent_scalarKernel
    (observation.coordinate / 2) w decay]
  exact burnolAnalyticComplementDivisionJet_succ observation k beforeOrder w
    nonresonant

/-- Every strict preterminal stage still contains a positive power of the
same resonant coordinate, hence its target read is zero. -/
theorem burnolAnalyticComplementDivisionJet_at_eq_zero_of_lt
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolAnalyticComplementDivisionJet owner observation k
        (burnolAnalyticComplementDivisionCenter observation) = 0 := by
  have remainingPositive :
      0 < generatedRiemannXiZeroOrder owner observation.coordinate - k :=
    Nat.sub_pos_of_lt beforeOrder
  have remainingNe :
      generatedRiemannXiZeroOrder owner observation.coordinate - k ≠ 0 :=
    Nat.ne_of_gt remainingPositive
  simp [burnolAnalyticComplementDivisionJet, remainingNe]

/-- At the exact generated zero order, the division jet is definitionally
the cancellation-aware finite part already present in the analytic source. -/
theorem burnolAnalyticComplementDivisionJet_at_order
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    burnolAnalyticComplementDivisionJet owner observation
        (generatedRiemannXiZeroOrder owner observation.coordinate)
        (burnolAnalyticComplementDivisionCenter observation) =
      burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) := by
  simp [burnolAnalyticComplementDivisionJet,
    burnolAnalyticComplementDivisionCenter,
    burnolAnalyticComplementIteratedResolventFinitePart]

/-- The existing finite-part evaluation is nonzero without any simple-zero
or physical-read premise. -/
theorem burnolAnalyticComplementIteratedResolventFinitePart_at_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) ≠ 0 := by
  rw [burnolAnalyticComplementIteratedResolventFinitePart_at
    observation nontrivial]
  have gammaSelectedNe : Gammaℝ observation.coordinate ≠ 0 :=
    observation.gammaReal_ne_zero_of_nontrivial nontrivial
  have gammaComplementNe : Gammaℝ (1 - observation.coordinate) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    linarith [observation.coordinate_re_lt_one]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (div_ne_zero gammaSelectedNe gammaComplementNe))
    (generatedRiemannBareZeroLocalizedSpectrum_at_ne_zero
      observation nontrivial)

/-- Exact-order scalar closure: all earlier reads vanish, while the final
read is the source-generated nonzero finite part. -/
theorem burnolAnalyticComplementDivisionZeroOrder_scalarLaw
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∀ k < generatedRiemannXiZeroOrder owner observation.coordinate,
      burnolAnalyticComplementDivisionJet owner observation k
        (burnolAnalyticComplementDivisionCenter observation) = 0) ∧
    burnolAnalyticComplementDivisionJet owner observation
        (generatedRiemannXiZeroOrder owner observation.coordinate)
        (burnolAnalyticComplementDivisionCenter observation) =
      burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) ∧
    burnolAnalyticComplementDivisionJet owner observation
        (generatedRiemannXiZeroOrder owner observation.coordinate)
        (burnolAnalyticComplementDivisionCenter observation) ≠ 0 := by
  refine ⟨?_, burnolAnalyticComplementDivisionJet_at_order observation, ?_⟩
  · intro k beforeOrder
    exact burnolAnalyticComplementDivisionJet_at_eq_zero_of_lt
      observation k beforeOrder
  · rw [burnolAnalyticComplementDivisionJet_at_order observation]
    exact burnolAnalyticComplementIteratedResolventFinitePart_at_ne_zero
      observation nontrivial

/-! ## Holomorphy of the source-generated scalar jet -/

private theorem divisionJet_differentiable_dslope_fixed
    (function : ℂ → ℂ) (center : ℂ)
    (entire : Differentiable ℂ function) :
    Differentiable ℂ (dslope function center) := by
  intro value
  by_cases atCenter : value = center
  · subst value
    have analytic : AnalyticAt ℂ function center :=
      (analyticOnNhd_univ_iff_differentiable.mpr entire) center
        (Set.mem_univ center)
    obtain ⟨series, expansion⟩ := analytic
    exact expansion.has_fpower_series_dslope_fslope.differentiableAt
  · exact (differentiableAt_dslope_of_ne atCenter).2 (entire value)

private theorem divisionJet_differentiable_generatedRiemannXi_iterate_dslope
    (owner : GlobalGermOwner) (center : ℂ) (order : ℕ) :
    Differentiable ℂ
      ((Function.swap dslope center)^[order] (generatedRiemannXi owner)) := by
  induction order with
  | zero => simpa using differentiable_generatedRiemannXi owner
  | succ order inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact divisionJet_differentiable_dslope_fixed
        _ center inductionHypothesis

private theorem divisionJet_differentiable_generatedRiemannXiZeroLocalization
    (owner : GlobalGermOwner) (center : ℂ) :
    Differentiable ℂ
      (generatedRiemannXiZeroLocalization owner center) := by
  unfold generatedRiemannXiZeroLocalization
  exact divisionJet_differentiable_generatedRiemannXi_iterate_dslope
    owner center _

private theorem
    divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum
    (owner : GlobalGermOwner) (center value : ℂ)
    (positive : 0 < value.re) (belowOne : value.re < 1) :
    DifferentiableAt ℂ
      (generatedRiemannBareZeroLocalizedSpectrum owner center) value := by
  have valueNeZero : value ≠ 0 := by
    intro zero
    subst value
    norm_num at positive
  have oneSubNe : 1 - value ≠ 0 := by
    intro zero
    have valueOne : value = 1 := (sub_eq_zero.mp zero).symm
    subst value
    norm_num at belowOne
  have denominatorNe : value * (1 - value) ≠ 0 :=
    mul_ne_zero valueNeZero oneSubNe
  have numeratorDifferentiable : DifferentiableAt ℂ
      (generatedRiemannXiZeroLocalization owner center) value :=
    divisionJet_differentiable_generatedRiemannXiZeroLocalization
      owner center value
  have alternativeDifferentiable : DifferentiableAt ℂ
      (fun current : ℂ =>
        generatedRiemannXiZeroLocalization owner center current *
            (Gammaℝ current)⁻¹ /
          (current * (1 - current))) value := by
    exact (numeratorDifferentiable.mul
      differentiable_Gammaℝ_inv.differentiableAt).div
        (differentiableAt_id.mul
          ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id))
        denominatorNe
  apply alternativeDifferentiable.congr_of_eventuallyEq
  filter_upwards with current
  unfold generatedRiemannBareZeroLocalizedSpectrum
  rw [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem
    divisionJet_differentiableAt_burnolAnalyticComplementQuarterQuotient
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (value : ℂ) (positive : 0 < value.re)
    (belowHalf : value.re < 1 / 2) :
    DifferentiableAt ℂ
      (burnolAnalyticComplementQuarterQuotient owner observation) value := by
  have doubledPositive : 0 < (2 * value).re := by
    simp only [mul_re]
    norm_num
    linarith
  have doubledBelowOne : (2 * value).re < 1 := by
    simp only [mul_re]
    norm_num
    linarith
  have doubledDifferentiable : DifferentiableAt ℂ
      (fun current : ℂ => 2 * current) value :=
    (differentiableAt_const (2 : ℂ)).mul differentiableAt_id
  have bareDifferentiable : DifferentiableAt ℂ
      (fun current : ℂ =>
        generatedRiemannBareZeroLocalizedSpectrum owner
          (1 - observation.coordinate) (2 * current)) value :=
    (divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum
      owner (1 - observation.coordinate) (2 * value)
      doubledPositive doubledBelowOne).comp value doubledDifferentiable
  have sourceDifferentiable : DifferentiableAt ℂ
      (fun current : ℂ =>
        coPoissonMuntzEvenSourceMellin
          (burnolAnalyticComplementNormalizedSource observation).1
          (2 * current)) value :=
    (coPoissonMuntzEvenSourceMellin_differentiableAt
      (burnolAnalyticComplementNormalizedSource observation).1
      (2 * value) doubledPositive).comp value doubledDifferentiable
  unfold burnolAnalyticComplementQuarterQuotient
    burnolCoordinateMatchedLocalizedSpectrum
  fun_prop

theorem differentiableAt_burnolAnalyticComplementDivisionJet
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (order : ℕ) (value : ℂ)
    (positive : 0 < value.re) (belowHalf : value.re < 1 / 2) :
    DifferentiableAt ℂ
      (burnolAnalyticComplementDivisionJet owner observation order) value := by
  unfold burnolAnalyticComplementDivisionJet
  have quotientDifferentiable :=
    divisionJet_differentiableAt_burnolAnalyticComplementQuarterQuotient
      observation value positive belowHalf
  exact (((differentiableAt_const ((-1 : ℂ) ^ order)).mul
    ((differentiableAt_id.sub
      (differentiableAt_const
        (burnolAnalyticComplementDivisionCenter observation))).pow
          (generatedRiemannXiZeroOrder owner observation.coordinate -
            order))).mul quotientDifferentiable)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
