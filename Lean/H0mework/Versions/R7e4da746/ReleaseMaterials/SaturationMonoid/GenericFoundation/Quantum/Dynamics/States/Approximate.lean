import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Asymptotic

/-! Near eigenvectors may carry a source energy phase. Conjugation removes
that phase, so their raw vector-state errors vanish on the whole bounded algebra. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

private theorem expectation_near {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖inner ℂ x (A x) - inner ℂ y (A y)‖ ≤ 2 * ‖A‖ * ‖x - y‖ := by
  have split : inner ℂ x (A x) - inner ℂ y (A y) =
      inner ℂ (x - y) (A x) + inner ℂ y (A (x - y)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [split]
  calc
    _ ≤ ‖inner ℂ (x - y) (A x)‖ + ‖inner ℂ y (A (x - y))‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * (‖A‖ * ‖x‖) + ‖y‖ * (‖A‖ * ‖x - y‖) :=
      add_le_add
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg _)))
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (A.le_opNorm (x - y)) (norm_nonneg _)))
    _ = _ := by rw [hx, hy]; ring

private theorem expectation_phase {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (v : H) (c : ℂ) (hc : ‖c‖ = 1) :
    inner ℂ (c • v) (A (c • v)) = inner ℂ v (A v) := by
  have unit : starRingEnd ℂ c * c = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, unit, one_mul]

private theorem expectation_conjugate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) (v : H) :
    inner ℂ v (U (A (U.symm v))) = inner ℂ (U.symm v) (A (U.symm v)) := by
  have same := U.inner_map_map (U.symm v) (A (U.symm v))
  simpa only [LinearIsometryEquiv.apply_symm_apply] using same

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]
  (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k))
  (v : ∀ k, E k) (normalized : ∀ k, ‖v k‖ = 1)

include normalized in
theorem vectorState_phase_bound (k : ℕ) (t : Multiplicative ℝ) (A : Bounded E)
    (c : ℂ) (hc : ‖c‖ = 1) :
    ‖vectorState E v k (action E U t A) - vectorState E v k A‖ ≤
      2 * ‖A‖ * ‖U k t⁻¹ (v k) - c • v k‖ := by
  have inverse : (U k t).symm = U k t⁻¹ := by
    change (U k t)⁻¹ = U k t⁻¹
    rw [map_inv]
  have hy : ‖c • v k‖ = 1 := by rw [norm_smul, hc, normalized k, one_mul]
  have hx : ‖(U k t).symm (v k)‖ = 1 :=
    ((U k t).symm.norm_map _).trans (normalized k)
  change ‖inner ℂ (v k) (action E U t A k (v k)) - inner ℂ (v k) (A k (v k))‖ ≤ _
  rw [action_apply_apply, expectation_conjugate,
    ← expectation_phase (A k) (v k) c hc]
  exact (expectation_near (A k) _ _ hx hy).trans (by
    rw [inverse]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (eval_norm_le E k A) (by norm_num)) (norm_nonneg _))

include normalized in
theorem vectorState_asymptotic_invariant
    (phase : ℕ → Multiplicative ℝ → ℂ) (unit : ∀ k t, ‖phase k t‖ = 1)
    (sourceLimit : ∀ t, Tendsto (fun k => ‖U k t (v k) - phase k t • v k‖) atTop (𝓝 0))
    (t : Multiplicative ℝ) (A : Bounded E) :
    Tendsto (fun k => vectorState E v k (action E U t A) - vectorState E v k A) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun k => vectorState_phase_bound E U v normalized k t A
    (phase k t⁻¹) (unit k t⁻¹))
  simpa only [mul_zero] using tendsto_const_nhds.mul (sourceLimit t⁻¹)

end
end SaturationMonoid.Quantum.Dynamics
