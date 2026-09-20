import H0mework.Quantum.Algebra.Bounded

/-! Coordinate conjugation preserves the actual bounded operator family.
Mathlib's operator conjugation generates the action of any parameter monoid.
The original time interface is its specialization; norm continuity is separate. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]

private def conjugate (V : ∀ k, E k ≃ₗᵢ[ℂ] E k) (A : Bounded E) : Bounded E :=
  ⟨fun k => (V k).conjStarAlgEquiv (A k), (lp.memℓp A).mono' fun k =>
    le_of_eq (StarAlgEquiv.norm_map (V k).conjStarAlgEquiv (A k))⟩

def pointwise (V : ∀ k, E k ≃ₗᵢ[ℂ] E k) : Bounded E ≃⋆ₐ[ℂ] Bounded E where
  toFun := conjugate E V
  invFun := conjugate E (fun k => (V k).symm)
  left_inv A := by
    apply lp.ext
    funext k
    exact (V k).conjStarAlgEquiv.symm_apply_apply (A k)
  right_inv A := by
    apply lp.ext
    funext k
    exact (V k).conjStarAlgEquiv.apply_symm_apply (A k)
  map_mul' A B := by
    apply lp.ext
    funext k
    exact (V k).conjStarAlgEquiv.map_mul (A k) (B k)
  map_add' A B := by
    apply lp.ext
    funext k
    exact (V k).conjStarAlgEquiv.map_add (A k) (B k)
  map_smul' c A := by
    apply lp.ext
    funext k
    exact map_smul (V k).conjStarAlgEquiv c (A k)
  map_star' A := by
    apply lp.ext
    funext k
    exact map_star (V k).conjStarAlgEquiv (A k)

theorem pointwise_apply (V : ∀ k, E k ≃ₗᵢ[ℂ] E k) (A : Bounded E) (k : ℕ) :
    pointwise E V A k = (V k).conjStarAlgEquiv (A k) := rfl

section Monoid

variable {Γ : Type*} [Monoid Γ] (U : ∀ k, Γ →* (E k ≃ₗᵢ[ℂ] E k))

def monoidAction : Γ →* (Bounded E ≃⋆ₐ[ℂ] Bounded E) where
  toFun t := pointwise E (fun k => U k t)
  map_one' := by
    apply StarAlgEquiv.ext
    intro A
    apply lp.ext
    funext k
    change (U k 1).conjStarAlgEquiv (A k) = A k
    rw [map_one]
    rfl
  map_mul' s t := by
    apply StarAlgEquiv.ext
    intro A
    apply lp.ext
    funext k
    change (U k (s * t)).conjStarAlgEquiv (A k) =
      (U k s).conjStarAlgEquiv ((U k t).conjStarAlgEquiv (A k))
    rw [map_mul]
    rfl

theorem monoidAction_apply (t : Γ) (A : Bounded E) (k : ℕ) :
    monoidAction E U t A k = (U k t).conjStarAlgEquiv (A k) := rfl

end Monoid

variable (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k))

def action : Multiplicative ℝ →* (Bounded E ≃⋆ₐ[ℂ] Bounded E) := monoidAction E U

theorem action_apply (t : Multiplicative ℝ) (A : Bounded E) (k : ℕ) :
    action E U t A k = (U k t).conjStarAlgEquiv (A k) := rfl

theorem action_apply_apply (t : Multiplicative ℝ) (A : Bounded E) (k : ℕ) (x : E k) :
    action E U t A k x = U k t (A k ((U k t).symm x)) := rfl

theorem action_eval (t : Multiplicative ℝ) (A : Bounded E) (k : ℕ) :
    eval E k (action E U t A) = (U k t).conjStarAlgEquiv (eval E k A) := rfl

theorem action_norm (t : Multiplicative ℝ) (A : Bounded E) : ‖action E U t A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (action E U t) A

theorem action_isometry (t : Multiplicative ℝ) : Isometry (action E U t) :=
  StarAlgEquiv.isometry (action E U t)

end
end SaturationMonoid.Quantum.Dynamics
