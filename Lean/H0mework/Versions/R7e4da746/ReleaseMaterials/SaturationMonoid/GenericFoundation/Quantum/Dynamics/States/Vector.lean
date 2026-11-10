import H0mework.Quantum.Algebra.Action

/-! Original unit vectors evaluate the actual operator coordinates. Their
fixed-vector law generates invariance under the same conjugation action. -/

set_option autoImplicit false

open scoped ENNReal InnerProductSpace ComplexOrder

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]
  (v : ∀ k, E k) (normalized : ∀ k, ‖v k‖ = 1)

def vectorState (k : ℕ) : Bounded E →L[ℂ] ℂ :=
  (innerSL ℂ (v k)).comp ((ContinuousLinearMap.apply ℂ (E k) (v k)).comp
    (lp.evalCLM ℂ (fun j => E j →L[ℂ] E j) ∞ k))

theorem vectorState_apply (k : ℕ) (A : Bounded E) :
    vectorState E v k A = inner ℂ (v k) (A k (v k)) := rfl

include normalized in
theorem vectorState_one (k : ℕ) : vectorState E v k 1 = 1 := by
  change inner ℂ (v k) (v k) = 1
  simp [inner_self_eq_norm_sq_to_K, normalized k]

theorem vectorState_star_mul (k : ℕ) (A : Bounded E) :
    vectorState E v k (star A * A) = ((‖A k (v k)‖ ^ 2 : ℝ) : ℂ) := by
  change inner ℂ (v k) ((A k).adjoint (A k (v k))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  convert! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (A k (v k)) using 1
  exact Complex.ofReal_pow _ _

theorem vectorState_positive (k : ℕ) (A : Bounded E) : 0 ≤ vectorState E v k (star A * A) := by
  rw [vectorState_star_mul]
  exact_mod_cast (sq_nonneg ‖A k (v k)‖)

include normalized in
theorem vectorState_bound (k : ℕ) (A : Bounded E) : ‖vectorState E v k A‖ ≤ ‖A‖ := by
  rw [vectorState_apply]
  calc
    _ ≤ ‖v k‖ * ‖A k (v k)‖ := norm_inner_le_norm _ _
    _ = ‖A k (v k)‖ := by rw [normalized k, one_mul]
    _ ≤ ‖A k‖ * ‖v k‖ := (A k).le_opNorm (v k)
    _ = ‖A k‖ := by rw [normalized k, mul_one]
    _ ≤ ‖A‖ := eval_norm_le E k A

include normalized in
theorem vectorState_norm_le_one (k : ℕ) : ‖vectorState E v k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun A => by
    simpa only [one_mul] using vectorState_bound E v normalized k A)

variable (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k))
  (fixed : ∀ k t, U k t (v k) = v k)

include fixed in
theorem vectorState_invariant (k : ℕ) (t : Multiplicative ℝ) (A : Bounded E) :
    vectorState E v k (action E U t A) = vectorState E v k A := by
  have inverse : (U k t).symm (v k) = v k := by
    apply (U k t).injective
    rw [LinearIsometryEquiv.apply_symm_apply, fixed]
  rw [vectorState_apply, vectorState_apply, action_apply_apply, inverse]
  have equality := (U k t).inner_map_map (v k) (A k (v k))
  rw [fixed] at equality
  exact equality

end
end SaturationMonoid.Quantum.Dynamics
