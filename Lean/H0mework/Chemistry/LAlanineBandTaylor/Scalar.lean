import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open Set
open scoped BigOperators

/-- The segment parameter runs from zero to one; it is not physical time. -/
theorem scalar_unit_taylor (f : ℝ → ℝ) (n : ℕ) (hf : ContDiff ℝ (n + 1) f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f 1 =
      (∑ k ∈ Finset.range (n + 1), iteratedDeriv k f 0 / (k.factorial : ℝ)) +
        iteratedDeriv (n + 1) f t / ((n + 1).factorial : ℝ) := by
  obtain ⟨t, ht, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := 0) (x := 1) (n := n) (by norm_num) hf.contDiffOn
  have hp : taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1 =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f 0 / (k.factorial : ℝ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have order : k ≤ n + 1 := (Finset.mem_range.mp hk).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1))
      (hf.of_le (by exact_mod_cast order)).contDiffAt (by norm_num)]
    simp [div_eq_mul_inv, mul_comm]
  rw [hp] at h
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
  refine ⟨t, ht', ?_⟩
  norm_num only [sub_zero, one_pow, mul_one] at h
  linarith

theorem scalar_unit_first (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f 1 = f 0 + deriv f 0 + iteratedDeriv 2 f t / 2 := by
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial] using
    scalar_unit_taylor f 1 hf

theorem scalar_unit_second (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f 1 = f 0 + deriv f 0 + iteratedDeriv 2 f 0 / 2 + iteratedDeriv 3 f t / 6 := by
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial] using
    scalar_unit_taylor f 2 hf

theorem scalar_first_remainder (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ)
    (bound : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv 2 f t| ≤ B) :
    |f 1 - (f 0 + deriv f 0)| ≤ B / 2 := by
  obtain ⟨t, ht, h⟩ := scalar_unit_first f hf
  have hb := bound t ⟨ht.1.le, ht.2.le⟩
  rw [h]
  simpa [abs_div] using
    div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2)

theorem scalar_second_remainder (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (B : ℝ)
    (bound : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv 3 f t| ≤ B) :
    |f 1 - (f 0 + deriv f 0 + iteratedDeriv 2 f 0 / 2)| ≤ B / 6 := by
  obtain ⟨t, ht, h⟩ := scalar_unit_second f hf
  have hb := bound t ⟨ht.1.le, ht.2.le⟩
  rw [h]
  simpa [abs_div] using
    div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 6)

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
