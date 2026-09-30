import H0mework.Arithmetic.CoPoisson.Energy

/-!
# Concrete annulus source for the co-Poisson energy map

A fixed smooth bump centered at `1/2`, vanishing for `|x| ≤ 1/4` and
`3/4 ≤ |x|`, has no integer samples and has strictly positive integral.  The actual Clozel
remainder therefore evaluates nontrivially on it.  On every nonnegative log
scale all nonzero lattice samples still vanish, which proves that the
existing co-Poisson log-orbit has a nonzero `L²` realization.

This source is independent of Mellin coordinates, zeta zeros, eigenvectors,
and physical landing data.  Its log-orbit is not identified here with
Burnol's additive co-sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped SchwartzMap ENNReal

noncomputable section

def burnolAnnulusBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def burnolAnnulusRealSchwartz : SchwartzMap ℝ ℝ :=
  burnolAnnulusBump.hasCompactSupport.toSchwartzMap
    burnolAnnulusBump.contDiff

def burnolAnnulusSchwartz : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM burnolAnnulusRealSchwartz

@[simp] theorem burnolAnnulusSchwartz_apply (x : ℝ) :
    burnolAnnulusSchwartz x = (burnolAnnulusBump x : ℂ) := by
  rfl

theorem burnolAnnulusBump_zero_of_abs_le_quarter
    {x : ℝ} (hx : |x| ≤ 1 / 4) :
    burnolAnnulusBump x = 0 := by
  apply burnolAnnulusBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist x (1 / 2)
  rw [Real.dist_eq]
  have bounds := abs_le.mp hx
  rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)]
  linarith

theorem burnolAnnulusBump_zero_of_three_quarters_le_abs
    {x : ℝ} (hx : 3 / 4 ≤ |x|) :
    burnolAnnulusBump x = 0 := by
  apply burnolAnnulusBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist x (1 / 2)
  rw [Real.dist_eq]
  rcases le_total x 0 with hx0 | hx0
  · rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)]
    linarith
  · rw [abs_of_nonneg hx0] at hx
    rw [abs_of_nonneg (by linarith : 0 ≤ x - 1 / 2)]
    linarith

/-- The concrete Schwartz source has literal annular support. -/
theorem burnolAnnulusSchwartz_support_subset :
    Function.support burnolAnnulusSchwartz ⊆
      {x : ℝ | 1 / 4 < |x| ∧ |x| < 3 / 4} := by
  intro x nonzero
  change burnolAnnulusSchwartz x ≠ 0 at nonzero
  constructor
  · by_contra notLower
    apply nonzero
    rw [burnolAnnulusSchwartz_apply,
      burnolAnnulusBump_zero_of_abs_le_quarter (le_of_not_gt notLower)]
    exact ofReal_zero
  · by_contra notUpper
    apply nonzero
    rw [burnolAnnulusSchwartz_apply,
      burnolAnnulusBump_zero_of_three_quarters_le_abs
        (le_of_not_gt notUpper)]
    exact ofReal_zero

theorem burnolAnnulusBump_integer_zero (n : ℤ) :
    burnolAnnulusBump (n : ℝ) = 0 := by
  by_cases zero : n = 0
  · subst n
    exact burnolAnnulusBump_zero_of_abs_le_quarter (by norm_num)
  · apply burnolAnnulusBump_zero_of_three_quarters_le_abs
    have oneLe : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs zero
    linarith

@[simp] theorem burnolAnnulusSchwartz_integer_tsum :
    (∑' n : ℤ, burnolAnnulusSchwartz n) = 0 := by
  rw [show (fun n : ℤ ↦ burnolAnnulusSchwartz n) = 0 by
    funext n
    rw [burnolAnnulusSchwartz_apply, burnolAnnulusBump_integer_zero]
    exact ofReal_zero]
  exact tsum_zero

theorem burnolAnnulusBump_integral_pos :
    0 < ∫ x : ℝ, burnolAnnulusBump x := by
  apply burnolAnnulusBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    burnolAnnulusBump.hasCompactSupport
    (by intro x; exact burnolAnnulusBump.nonneg' x)
    (x := (1 / 2 : ℝ))
  have one : burnolAnnulusBump (1 / 2 : ℝ) = 1 := by
    apply burnolAnnulusBump.one_of_mem_closedBall
    simp [burnolAnnulusBump]
  rw [one]
  exact one_ne_zero

theorem burnolAnnulusSchwartz_integral_ne_zero :
    (∫ x : ℝ, burnolAnnulusSchwartz x) ≠ 0 := by
  rw [show (∫ x : ℝ, burnolAnnulusSchwartz x) =
      ((∫ x : ℝ, burnolAnnulusBump x : ℝ) : ℂ) by
    simp_rw [burnolAnnulusSchwartz_apply]
    exact integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt burnolAnnulusBump_integral_pos)

theorem clozelTemperedRemainder_burnolAnnulus_value :
    clozelTemperedRemainder burnolAnnulusSchwartz =
      -(∫ x : ℝ, burnolAnnulusSchwartz x) := by
  rw [clozelTemperedRemainder_apply,
    burnolAnnulusSchwartz_integer_tsum]
  simp [burnolAnnulusBump_zero_of_abs_le_quarter (x := 0) (by norm_num)]

theorem clozelTemperedRemainder_burnolAnnulus_ne_zero :
    clozelTemperedRemainder burnolAnnulusSchwartz ≠ 0 := by
  rw [clozelTemperedRemainder_burnolAnnulus_value]
  exact neg_ne_zero.mpr burnolAnnulusSchwartz_integral_ne_zero

theorem burnolAnnulus_scaled_nonzero_lattice_zero
    {x : ℝ} (hx : 0 ≤ x) (n : {n : ℤ // n ≠ 0}) :
    burnolAnnulusSchwartz (Real.exp x * (n.1 : ℝ)) = 0 := by
  rw [burnolAnnulusSchwartz_apply]
  rw [burnolAnnulusBump_zero_of_three_quarters_le_abs]
  · exact ofReal_zero
  rw [abs_mul, abs_of_pos (Real.exp_pos x)]
  have oneLe : (1 : ℝ) ≤ |(n.1 : ℝ)| := by
    exact_mod_cast Int.one_le_abs n.2
  have expOne : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  nlinarith

theorem coPoissonLogOrbitMap_burnolAnnulus_ne_zero
    {x : ℝ} (hx : 0 ≤ x) :
    coPoissonLogOrbitMap burnolAnnulusSchwartz x ≠ 0 := by
  rw [coPoissonLogOrbitMap_nonzero_formula]
  have sumZero :
      (∑' n : {n : ℤ // n ≠ 0},
        burnolAnnulusSchwartz (Real.exp x * (n.1 : ℝ))) = 0 := by
    rw [show (fun n : {n : ℤ // n ≠ 0} ↦
        burnolAnnulusSchwartz (Real.exp x * (n.1 : ℝ))) = 0 by
      funext n
      exact burnolAnnulus_scaled_nonzero_lattice_zero hx n]
    exact tsum_zero
  rw [sumZero, zero_sub]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr <|
      Or.inl (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x))
  · exact neg_ne_zero.mpr (smul_ne_zero (Real.exp_ne_zero (-x))
      burnolAnnulusSchwartz_integral_ne_zero)

/-- Direct nonzero consumer of the actual annulus source in the existing
co-Poisson log-energy carrier. -/
theorem coPoissonLogOrbitEnergyMap_burnolAnnulus_ne_zero :
    coPoissonLogOrbitEnergyMap burnolAnnulusSchwartz ≠ 0 := by
  intro energyZero
  have energyAeZero :
      (coPoissonLogOrbitEnergyMap burnolAnnulusSchwartz : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ)] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp energyZero
  have orbitAeZero :
      coPoissonLogOrbitMap burnolAnnulusSchwartz =ᵐ[
        (volume : Measure ℝ)] 0 := by
    filter_upwards [
      coPoissonLogOrbitEnergyMap_coeFn burnolAnnulusSchwartz,
      energyAeZero] with x hcoe hzero
    exact hcoe.symm.trans hzero
  have intervalMeasure :
      (volume : Measure ℝ) (Ioo (0 : ℝ) 1) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨x, hx, hzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    intervalMeasure (ae_restrict_of_ae orbitAeZero)
  exact coPoissonLogOrbitMap_burnolAnnulus_ne_zero hx.1.le hzero

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
