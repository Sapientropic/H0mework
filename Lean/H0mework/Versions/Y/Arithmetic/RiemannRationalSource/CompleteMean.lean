import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.Ward
import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.Mass

/-! The original complete mean is part of the finite physical Ward, not a discarded term. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem secondFlux_integrated (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    4 * (∫ t : ℝ in (1 / 4)..4, source.1 t) =
      -secondFlux coordinate source (1 / 4) + coordinate.value * (1 - coordinate.value) *
        (∫ t : ℝ in (1 / 4)..4, secondCoefficient coordinate source t) := by
  have sourceInt : IntervalIntegrable source.1 volume (1 / 4) 4 :=
    source.1.continuous.intervalIntegrable (1 / 4) 4
  have secondInt : IntervalIntegrable (secondCoefficient coordinate source) volume (1 / 4) 4 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (fun t ht =>
      (secondCoefficient_derivative coordinate source ht.1).continuousAt.continuousWithinAt)
  have derivative (t : ℝ) (ht : t ∈ uIcc (1 / 4 : ℝ) 4) :=
    secondFlux_derivative coordinate source (by
      have interval : t ∈ Icc (1 / 4 : ℝ) 4 := by
        simpa only [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)] using ht
      exact interval.1)
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    ((sourceInt.const_mul 4).sub
      (secondInt.const_mul (coordinate.value * (1 - coordinate.value))))
  have split : (∫ t : ℝ in (1 / 4)..4,
      4 * source.1 t - coordinate.value * (1 - coordinate.value) * secondCoefficient coordinate source t) =
      (∫ t : ℝ in (1 / 4)..4, 4 * source.1 t) -
        (∫ t : ℝ in (1 / 4)..4,
          coordinate.value * (1 - coordinate.value) * secondCoefficient coordinate source t) :=
    intervalIntegral.integral_sub (sourceInt.const_mul 4)
      (secondInt.const_mul (coordinate.value * (1 - coordinate.value)))
  rw [split, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    secondFlux_outer] at generated
  linear_combination generated

theorem original_W_complete_mean_ward {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (N : ℕ) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    let mean := (1 / 2 : ℂ) * ∫ x : ℝ, W x
    4 * (∫ t : ℝ in (1 / 4)..4, source.1 t *
      ((∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) - mean)) =
      (∑ n ∈ Finset.range N, sourceReciprocalContactLoad coordinate source (n + 1)) +
        mean * secondFlux coordinate source (1 / 4) +
        ((2 * observation.coordinate - 1) / 2) *
          (∫ t : ℝ in (1 / 4)..4, secondCoefficient coordinate source t) := by
  intro coordinate one W mean
  have sourceInt : IntervalIntegrable source.1 volume (1 / 4) 4 :=
    source.1.continuous.intervalIntegrable (1 / 4) 4
  have samplesInt : IntervalIntegrable (fun t : ℝ => source.1 t *
      ∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t)
      volume (1 / 4) 4 := by
    simp_rw [Finset.mul_sum]
    have each (n : ℕ) : IntervalIntegrable (fun t : ℝ => source.1 t *
        burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) volume (1 / 4) 4 :=
      ((source.1.memLp 2 volume).integrable_mul
        (Lp.memLp (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n)))).intervalIntegrable
    convert! IntervalIntegrable.sum (Finset.range N) (fun n _ => each n) using 1
    ext t
    simp only [Finset.sum_apply]
  have split : (∫ t : ℝ in (1 / 4)..4,
      (source.1 t * ∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) -
        source.1 t * mean) =
      (∫ t : ℝ in (1 / 4)..4, source.1 t *
        ∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) -
          (∫ t : ℝ in (1 / 4)..4, source.1 t * mean) :=
    intervalIntegral.integral_sub samplesInt (sourceInt.mul_const mean)
  have mass : mean * (coordinate.value * (1 - coordinate.value)) =
      -(2 * observation.coordinate - 1) / 2 := by
    have sn : observation.coordinate ≠ 0 := by
      intro zero
      have re := congrArg Complex.re zero
      simp only [Complex.zero_re] at re
      linarith
    have on : 1 - observation.coordinate ≠ 0 := by
      intro zero
      have re := congrArg Complex.re zero
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at re
      have below : observation.coordinate.re < 1 := coordinate.belowOne
      linarith
    change ((1 / 2 : ℂ) * (∫ x : ℝ, W x)) *
      (observation.coordinate * (1 - observation.coordinate)) = _
    rw [burnolZeroOwnedUnitOnePair_integral observation nontrivial rightHalf]
    field_simp [sn, on]
    ring
  have generated := original_W_finite_sampling_ward observation nontrivial rightHalf source N
  have sourceEquation := secondFlux_integrated coordinate source
  simp_rw [mul_sub]
  rw [split, intervalIntegral.integral_mul_const]
  linear_combination generated - mean * sourceEquation -
    (∫ t : ℝ in (1 / 4)..4, secondCoefficient coordinate source t) * mass

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
