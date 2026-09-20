import Mathlib.Analysis.Fourier.PoissonSummation
import H0mework.Arithmetic.Tempered.Scaling

/-!
# Clozel tempered remainder

This module realizes the integer Dirac comb as an actual tempered distribution,
proves its evaluation formula, and uses Poisson summation to identify its
Fourier transform.  It then constructs the nonzero-lattice remainder and proves
its Fourier invariance.

These operator identities do not assert that the comb, the remainder, or any
evaluation of the remainder vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open FourierTransform MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

/-- Counting measure on `ℤ`, pushed forward along the standard embedding into `ℝ`. -/
def integerCombMeasure : Measure ℝ :=
  Measure.map (fun n : ℤ => (n : ℝ)) Measure.count

/-- The integer comb has temperate growth, witnessed by quadratic decay. -/
instance integerCombMeasure_hasTemperateGrowth :
    integerCombMeasure.HasTemperateGrowth where
  exists_integrable := by
    refine ⟨2, ?_⟩
    unfold integerCombMeasure
    refine (integrable_map_measure ?_
      (measurable_of_countable _).aemeasurable).2 ?_
    · exact ((continuous_const.add continuous_norm).rpow_const
        (fun x : ℝ => Or.inl (by
          simp only [Pi.add_apply]
          positivity))).aestronglyMeasurable
    · rw [integrable_count_iff]
      change Summable (fun n : ℤ =>
        ‖(1 + ‖(n : ℝ)‖) ^ (-(2 : ℝ))‖)
      rw [summable_int_iff_summable_nat_and_neg]
      constructor
      · have source :=
          (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
        refine source.congr ?_
        intro n
        rw [Real.norm_rpow_of_nonneg (by positivity)]
        rw [Real.norm_of_nonneg (by positivity)]
        rw [Real.rpow_neg (by positivity)]
        simp [add_comm]
      · have source :=
          (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
        refine source.congr ?_
        intro n
        rw [Real.norm_rpow_of_nonneg (by positivity)]
        rw [Real.norm_of_nonneg (by positivity)]
        rw [Real.rpow_neg (by positivity)]
        simp [add_comm]

/-- The actual tempered distribution attached to the integer comb measure. -/
def integerDiracComb : ComplexTempered :=
  integerCombMeasure.toTemperedDistribution

@[simp]
theorem integerDiracComb_apply (phi : 𝓢(ℝ, ℂ)) :
    integerDiracComb phi = ∑' n : ℤ, phi n := by
  unfold integerDiracComb
  change (∫ x : ℝ, phi x ∂integerCombMeasure) = _
  unfold integerCombMeasure
  rw [integral_map (measurable_of_countable _).aemeasurable
    phi.continuous.aestronglyMeasurable]
  have hphi : Integrable (fun n : ℤ => phi (n : ℝ)) Measure.count := by
    exact (integrable_map_measure phi.continuous.aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).1
        (show Integrable phi integerCombMeasure from phi.integrable)
  rw [integral_countable hphi]
  simp

/-- Integer samples of a Schwartz function are absolutely summable. -/
theorem summable_integer_evaluation (phi : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => phi (n : ℝ)) := by
  have hphi : Integrable (fun n : ℤ => phi (n : ℝ)) Measure.count := by
    exact (integrable_map_measure phi.continuous.aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).1
        (show Integrable phi integerCombMeasure from phi.integrable)
  exact summable_norm_iff.mp (integrable_count_iff.mp hphi)

/-- Poisson summation identifies the Fourier transform of the integer comb. -/
theorem fourier_integerDiracComb :
    𝓕 integerDiracComb = integerDiracComb := by
  ext phi
  rw [TemperedDistribution.fourier_apply]
  rw [integerDiracComb_apply, integerDiracComb_apply]
  have poisson := SchwartzMap.tsum_eq_tsum_fourier phi 0
  simpa using poisson.symm

/-- Under Mathlib's self-dual real Fourier normalization, volume transforms to `delta 0`. -/
theorem fourier_volume_toTemperedDistribution :
    𝓕 (volume.toTemperedDistribution : ComplexTempered) =
      TemperedDistribution.delta 0 := by
  rw [← TemperedDistribution.fourier_delta_zero (E := ℝ)]
  ext phi
  simp only [TemperedDistribution.fourier_apply,
    TemperedDistribution.delta_apply]
  have inversionMap : 𝓕⁻ (𝓕 phi) = phi :=
    fourierInv_fourier_eq phi
  rw [SchwartzMap.fourierInv_apply_eq] at inversionMap
  have inversion := congrArg (fun psi : 𝓢(ℝ, ℂ) => psi 0) inversionMap
  simpa using inversion

/-- Clozel's remainder: the nonzero integer comb minus volume. -/
def clozelTemperedRemainder : ComplexTempered :=
  integerDiracComb - TemperedDistribution.delta 0 -
    volume.toTemperedDistribution

@[simp]
theorem clozelTemperedRemainder_apply (phi : 𝓢(ℝ, ℂ)) :
    clozelTemperedRemainder phi =
      (∑' n : ℤ, phi n) - phi 0 - ∫ x : ℝ, phi x := by
  simp [clozelTemperedRemainder]

/-- Equivalent nonzero-lattice form of the remainder. -/
theorem clozelTemperedRemainder_apply_nonzero (phi : 𝓢(ℝ, ℂ)) :
    clozelTemperedRemainder phi =
      (∑' n : {n : ℤ // n ≠ 0}, phi n) - ∫ x : ℝ, phi x := by
  rw [clozelTemperedRemainder_apply]
  have split :=
    (summable_integer_evaluation phi).sum_add_tsum_subtype_compl
      ({0} : Finset ℤ)
  simp only [Finset.sum_singleton] at split
  let nonzeroEquiv :
      {n : ℤ // n ∉ ({0} : Finset ℤ)} ≃ {n : ℤ // n ≠ 0} := {
    toFun n := ⟨n, by simpa using n.property⟩
    invFun n := ⟨n, by simpa using n.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  have reindex :
      (∑' n : {n : ℤ // n ∉ ({0} : Finset ℤ)}, phi n) =
        ∑' n : {n : ℤ // n ≠ 0}, phi n := by
    simpa [nonzeroEquiv] using
      nonzeroEquiv.tsum_eq (fun n : {n : ℤ // n ≠ 0} => phi n)
  rw [← split]
  rw [reindex]
  norm_num

/-- Fourier exchanges `delta 0` and volume, so their symmetric removal stays fixed. -/
theorem fourier_clozelTemperedRemainder :
    𝓕 clozelTemperedRemainder = clozelTemperedRemainder := by
  unfold clozelTemperedRemainder
  simp only [sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg]
  rw [fourier_integerDiracComb,
    TemperedDistribution.fourier_delta_zero (E := ℝ),
    fourier_volume_toTemperedDistribution]
  abel

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
