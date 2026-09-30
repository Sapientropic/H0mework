import H0mework.Chemistry.LAlanineBandTaylor.Segment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel Set
noncomputable section

theorem abs_map_sum_le {ι : Type*} (L : List ι) (f g : ι → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ g a) : |(L.map f).sum| ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb]))))

theorem factorial_positive (a : MultiIndex) : (0 : ℝ) < (factorial a : ℝ) := by
  unfold factorial
  positivity

theorem monomial_abs_le (a : MultiIndex) (v r : Point) (hr : ∀ i, |v i| ≤ r i) :
    |monomial a v| ≤ monomial a r := by
  have h0 := pow_le_pow_left₀ (abs_nonneg (v 0)) (hr 0) (a 0)
  have h1 := pow_le_pow_left₀ (abs_nonneg (v 1)) (hr 1) (a 1)
  have h2 := pow_le_pow_left₀ (abs_nonneg (v 2)) (hr 2) (a 2)
  simp only [monomial, abs_mul, abs_pow]
  exact mul_le_mul
    (mul_le_mul h0 h1 (pow_nonneg (abs_nonneg _) _) (pow_nonneg ((abs_nonneg _).trans (hr 0)) _)) h2
    (pow_nonneg (abs_nonneg _) _)
    (mul_nonneg (pow_nonneg ((abs_nonneg _).trans (hr 0)) _) (pow_nonneg ((abs_nonneg _).trans (hr 1)) _))

theorem homogeneous_abs_le (n : ℕ) (f B : MultiIndex → ℝ) (m : MultiIndex) (v r : Point)
    (hr : ∀ i, |v i| ≤ r i)
    (bound : ∀ a ∈ increments n, |f (shift m a)| ≤ B (shift m a)) :
    |homogeneous n f m v| ≤ homogeneous n B m r := by
  apply abs_map_sum_le
  intro a ha
  rw [abs_div, abs_mul, abs_of_pos (factorial_positive a)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (bound a ha) (monomial_abs_le a v r hr) (abs_nonneg _)
      ((abs_nonneg _).trans (bound a ha))) (factorial_positive a).le

/-- Source fourth jets control the complete mixed remainder on the same segment. -/
theorem densityJet_remainder (n : Fin 3) (m : MultiIndex) (c v r : Point) (B : MultiIndex → ℝ)
    (hr : ∀ i, |v i| ≤ r i)
    (bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a ∈ increments (n.val+1),
      |densityJet (shift m a) (segment c v t)| ≤ B (shift m a)) :
    |densityJet m (c+v) - polynomial n.val (fun j => densityJet j c) m v| ≤
      homogeneous (n.val+1) B m r := by
  obtain ⟨t, ht, h⟩ := densityJet_taylor n m c v
  rw [h, add_sub_cancel_left]
  exact homogeneous_abs_le _ _ _ _ _ _ hr (bound t ⟨ht.1.le,ht.2.le⟩)

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
