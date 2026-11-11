import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticMomentGram

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

/-- The monomials live in the original q interval, before its actual mean projection. -/
def powerRaw (n : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ (2 * n)

theorem power_memLp (n : ℕ) : MemLp (powerRaw n) 2 μq := by
  have regular : Continuous (powerRaw n) := by unfold powerRaw; fun_prop
  apply (memLp_two_iff_integrable_sq_norm regular.aestronglyMeasurable).mpr
  exact (regular.norm.pow 2).integrableOn_Icc

def powerL2 (n : ℕ) : Hq := (power_memLp n).toLp (powerRaw n)

theorem power_coeFn (n : ℕ) : (powerL2 n : ℝ → ℂ) =ᵐ[μq] powerRaw n :=
  (power_memLp n).coeFn_toLp

def centeredPower (n : ℕ) : M := Constructor.zeroMean (powerL2 n)

theorem power_integral (n : ℕ) :
    (∫ x : ℝ in symmetricInterval q, powerRaw n x) =
      2 * (q : ℂ) ^ (2 * n + 1) / (2 * (n : ℂ) + 1) := by
  have negative : (-q) ^ (2 * n + 1) = -(q ^ (2 * n + 1)) := by
    simp only [pow_succ, pow_mul]
    ring
  simp only [powerRaw, ← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  change (((∫ x : ℝ in Icc (-q) q, x ^ (2 * n)) : ℝ) : ℂ) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    integral_pow, negative]
  push_cast
  ring

theorem power_mean (n : ℕ) :
    burnolQuarterMeanCoefficient (powerL2 n) = (q : ℂ) ^ (2 * n) / (2 * (n : ℂ) + 1) := by
  rw [Constructor.mean_integral, integral_congr_ae (power_coeFn n), power_integral, pow_succ]
  norm_num
  ring

theorem centered_coeFn (n : ℕ) : (centeredPower n : Hq) =ᵐ[μq]
    fun x : ℝ => (x : ℂ) ^ (2 * n) - (q : ℂ) ^ (2 * n) / (2 * (n : ℂ) + 1) := by
  have source := Constructor.zeroMean_read (powerL2 n)
  change (centeredPower n : Hq) = _ at source
  rw [source, power_mean]
  filter_upwards [Lp.coeFn_sub (powerL2 n)
      (((q : ℂ) ^ (2 * n) / (2 * (n : ℂ) + 1)) • intervalConstant q),
    power_coeFn n, Lp.coeFn_smul ((q : ℂ) ^ (2 * n) / (2 * (n : ℂ) + 1)) (intervalConstant q),
    intervalConstant_coeFn q] with x subAt power scaled constant
  rw [subAt]
  change powerL2 n x - (((q : ℂ) ^ (2 * n) / (2 * (n : ℂ) + 1)) • intervalConstant q) x = _
  rw [scaled]
  simp only [Pi.smul_apply, smul_eq_mul, power, powerRaw, constant, mul_one]

theorem centered_zero : centeredPower 0 = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [centered_coeFn 0,
    Lp.coeFn_zero ℂ 2 μq] with x read zero
  change (centeredPower 0 : Hq) x = (0 : Hq) x
  rw [zero]
  simpa using read

private theorem power_inner (j k : ℕ) :
    inner ℂ (powerL2 j) (powerL2 k) =
      2 * (q : ℂ) ^ (2 * j + 2 * k + 1) / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) := by
  have source : (fun x : ℝ => inner ℂ (powerL2 j x) (powerL2 k x)) =ᵐ[μq] powerRaw (j + k) := by
    filter_upwards [power_coeFn j, power_coeFn k] with x left right
    rw [left, right, RCLike.inner_apply]
    simp only [powerRaw, map_pow, Complex.conj_ofReal, Nat.mul_add]
    rw [pow_add]
    ring
  rw [L2.inner_def, integral_congr_ae source, power_integral]
  push_cast
  simp only [Nat.mul_add]
  ring

private theorem power_constant (n : ℕ) :
    inner ℂ (powerL2 n) (intervalConstant q) =
      2 * (q : ℂ) ^ (2 * n + 1) / (2 * (n : ℂ) + 1) := by
  rw [L2.inner_def]
  have source : (fun x : ℝ => inner ℂ (powerL2 n x) (intervalConstant q x)) =ᵐ[μq] powerRaw n := by
    filter_upwards [power_coeFn n, intervalConstant_coeFn q] with x power constant
    rw [power, constant, RCLike.inner_apply]
    simp only [powerRaw, map_pow, Complex.conj_ofReal, one_mul]
  rw [integral_congr_ae source, power_integral]

/-- The actual q integral supplies every entry; no coefficient-space metric is chosen. -/
theorem inner_centered (j k : ℕ) :
    inner ℂ (centeredPower j : Hq) (centeredPower k : Hq) =
      2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
        (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
          1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1))) := by
  have drop := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (centeredPower k) (powerL2 j)
  change inner ℂ (centeredPower j : Hq) (centeredPower k : Hq) = inner ℂ (powerL2 j) (centeredPower k : Hq) at drop
  rw [drop]
  change inner ℂ (powerL2 j) (Constructor.zeroMean (powerL2 k) : Hq) = _
  rw [Constructor.zeroMean_read, inner_sub_right, inner_smul_right, power_inner, power_mean, power_constant]
  have exponents : (q : ℂ) ^ (2 * k) * (q : ℂ) ^ (2 * j + 1) = (q : ℂ) ^ (2 * j + 2 * k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = 2 * (q : ℂ) ^ (2 * j + 2 * k + 1) / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
        2 * ((q : ℂ) ^ (2 * k) * (q : ℂ) ^ (2 * j + 1)) /
          ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
    _ = _ := by rw [exponents]; ring

/-- Finite source coefficients are read with the Gram matrix generated by the same q integral. -/
theorem finite_gram (indices : Finset ℕ) (left right : ℕ → ℂ) :
    inner ℂ (∑ j ∈ indices, left j • (centeredPower j : Hq)) (∑ k ∈ indices, right k • (centeredPower k : Hq)) =
      ∑ j ∈ indices, ∑ k ∈ indices, star (left j) * right k *
        (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
          (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
            1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [inner_smul_right, inner_centered]
  simp only [starRingEnd_apply]
  ring

theorem finite_norm (indices : Finset ℕ) (coefficient : ℕ → ℂ) :
    (‖∑ j ∈ indices, coefficient j • (centeredPower j : Hq)‖ ^ 2 : ℂ) =
      ∑ j ∈ indices, ∑ k ∈ indices, star (coefficient j) * coefficient k *
        (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
          (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
            1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  simpa only [inner_self_eq_norm_sq_to_K] using! finite_gram indices coefficient coefficient

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticMomentGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
