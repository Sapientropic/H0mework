import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.HMellin

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private def box (s : ℂ) (a x : ℝ) : ℂ := (x : ℂ) ^ (-s) * ConstantDual.seedRaw (a * x)

private theorem box_indicator (s : ℂ) (a : ℝ) (positive : 0 < a) :
    box s a =ᵐ[volume.restrict (Ioi 0)] (Ioc 0 (q / a)).indicator (fun x : ℝ => (x : ℂ) ^ (-s)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have incidence : |a * x| ≤ q ↔ x ∈ Ioc 0 (q / a) := by
    rw [abs_of_pos (mul_pos positive hx), mem_Ioc, and_iff_right (show 0 < x from hx), le_div_iff₀ positive, mul_comm]
  by_cases inside : x ∈ Ioc 0 (q / a)
  · rw [box, ConstantDual.seedRaw, if_pos (incidence.mpr inside), mul_one, indicator_of_mem inside]
  · rw [box, ConstantDual.seedRaw, if_neg (fun h => inside (incidence.mp h)), mul_zero, indicator_of_notMem inside]

private theorem box_integrable (s : ℂ) (below : s.re < 1) (a : ℝ) (positive : 0 < a) :
    IntegrableOn (box s a) (Ioi 0) := by
  have power : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioc 0 (q / a)) := by
    have actual := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := q / a)
      (show -1 < (-s).re by simp only [neg_re]; linarith)).def'
    rwa [uIoc_of_le (by positivity : (0 : ℝ) ≤ q / a)] at actual
  have integral : Integrable ((Ioc 0 (q / a)).indicator (fun x : ℝ => (x : ℂ) ^ (-s)))
      (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    exact power
  exact integral.congr (box_indicator s a positive).symm

private theorem notOne (s : ℂ) (below : s.re < 1) : 1 - s ≠ 0 := by
  intro equality
  have re := congrArg Complex.re equality
  simp only [sub_re, one_re, zero_re] at re
  linarith

/-- Each actual integer box is integrated before any arithmetic limit is used. -/
theorem box_integral (s : ℂ) (below : s.re < 1) (a : ℝ) (positive : 0 < a) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s) * ConstantDual.seedRaw (a * x)) =
      (q : ℂ) ^ (1 - s) / (1 - s) * (a : ℂ) ^ (s - 1) := by
  change (∫ x : ℝ in Ioi 0, box s a x) = _
  rw [integral_congr_ae (box_indicator s a positive), integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ q / a),
    integral_cpow (Or.inl (show -1 < (-s).re by simp only [neg_re]; linarith)),
    show -s + 1 = 1 - s by ring, Complex.ofReal_zero, zero_cpow (notOne s below), sub_zero,
    Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ q) positive.le]
  simp only [div_eq_mul_inv, ← cpow_neg, neg_sub]
  ring

private theorem box_norm_integral (s : ℂ) (below : s.re < 1) (a : ℝ) (positive : 0 < a) :
    (∫ x : ℝ in Ioi 0, ‖box s a x‖) = q ^ (1 - s.re) / (1 - s.re) * a ^ (s.re - 1) := by
  have same : (fun x : ℝ => ‖box s a x‖) =ᵐ[volume.restrict (Ioi 0)]
      (Ioc 0 (q / a)).indicator (fun x : ℝ => x ^ (-s.re)) := by
    filter_upwards [box_indicator s a positive, ae_restrict_mem measurableSet_Ioi] with x source hx
    rw [source]
    by_cases inside : x ∈ Ioc 0 (q / a)
    · rw [indicator_of_mem inside, indicator_of_mem inside, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside, norm_zero]
  rw [integral_congr_ae same, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ q / a),
    integral_rpow (Or.inl (by linarith : -1 < -s.re)),
    show -s.re + 1 = 1 - s.re by ring, Real.zero_rpow (by linarith : 1 - s.re ≠ 0), sub_zero,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ q) positive.le]
  simp only [div_eq_mul_inv, ← Real.rpow_neg positive.le, neg_sub]
  ring

private theorem joint_integrable (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) (N : ℕ) :
    Integrable (fun point : ℝ × ℝ => box s point.1 point.2)
      ((volume.restrict (Ioc 0 (N : ℝ))).prod (volume.restrict (Ioi 0))) := by
  have measured : Measurable (fun point : ℝ × ℝ => box s point.1 point.2) := by
    unfold box
    apply Measurable.mul _ (ConstantDual.seedRaw_measurable.comp (by fun_prop))
    fun_prop
  apply (integrable_prod_iff measured.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a located
    exact box_integrable s below a located.1
  · have power := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := (N : ℝ))
      (by linarith : -1 < s.re - 1)).def'
    rw [uIoc_of_le (Nat.cast_nonneg N)] at power
    apply (power.const_mul (q ^ (1 - s.re) / (1 - s.re))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a located
    exact (box_norm_integral s below a located.1).symm

/-- The complete continuous channel is integrated, including both sides of its q/N seam. -/
theorem continuous_integral (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) (N : ℕ) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s) *
      ∫ a : ℝ in Ioc 0 (N : ℝ), ConstantDual.seedRaw (a * x)) =
      (q : ℂ) ^ (1 - s) / (1 - s) * (N : ℂ) ^ s / s := by
  have actual := integral_integral_swap (f := fun a x => box s a x) (joint_integrable s positive below N)
  simp only [box, integral_const_mul] at actual
  rw [← actual]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => box_integral s below a inside.1), integral_const_mul,
    ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    integral_cpow (Or.inl (show -1 < (s - 1).re by simp only [sub_re, one_re]; linarith)), sub_add_cancel,
    Complex.ofReal_zero, zero_cpow (by intro h; simp [h] at positive), sub_zero]
  push_cast
  ring

/-- The same original finite integer-minus-continuous source supplies its exact Mellin coefficient. -/
theorem finite_integral (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) (N : ℕ) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s) * ConstantDual.finiteRaw N x) =
      (q : ℂ) ^ (1 - s) / (1 - s) * FiniteForcing.coefficient (1 - s) N := by
  have terms (n : ℕ) (inside : n ∈ Finset.Ico 1 N) : IntegrableOn (box s n) (Ioi 0) :=
    box_integrable s below n (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  have integral : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s) *
      ∫ a : ℝ in Ioc 0 (N : ℝ), ConstantDual.seedRaw (a * x)) (Ioi 0) := by
    simpa only [box, integral_const_mul] using! (joint_integrable s positive below N).integral_prod_right
  calc
    _ = ∫ x : ℝ in Ioi 0, (∑ n ∈ Finset.Ico 1 N, box s n x) -
        (x : ℂ) ^ (-s) * ∫ a : ℝ in Ioc 0 (N : ℝ), ConstantDual.seedRaw (a * x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← ConstantDual.raw_eq_finite N x hx.ne', ConstantDual.raw, mul_sub, Finset.mul_sum]
      rfl
    _ = (∑ n ∈ Finset.Ico 1 N, (q : ℂ) ^ (1 - s) / (1 - s) * (n : ℂ) ^ (s - 1)) -
        (q : ℂ) ^ (1 - s) / (1 - s) * (N : ℂ) ^ s / s := by
      rw [integral_sub (integrable_finsetSum _ terms) integral, integral_finsetSum _ terms,
        continuous_integral s positive below N]
      congr 1
      exact Finset.sum_congr rfl (fun n inside => box_integral s below n
        (by exact_mod_cast (Finset.mem_Ico.mp inside).1))
    _ = _ := by
      rw [← Finset.mul_sum, FiniteForcing.coefficient, sub_sub_cancel, neg_sub]
      ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.HMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
