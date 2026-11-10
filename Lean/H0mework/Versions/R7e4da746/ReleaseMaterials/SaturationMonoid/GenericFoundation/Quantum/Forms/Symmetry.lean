import H0mework.Realization.Perfectification.Quantum.Forms.Graph

/-! The old graph projection consumes the invariant source form directly.
No action on an auxiliary gradient carrier or Hamiltonian domain is input. -/

set_option autoImplicit false
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Forms.Graph.Symmetry

noncomputable section

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)

theorem solution_unique (x : H) (y : A.domain)
    (weak : ∀ z : A.domain, inner ℂ (x-y.val) z.val = inner ℂ (A y) (A z)) :
    y.val = resolvent A closed x := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  have projected : projection A closed (lift x) = WithLp.toLp 2 (y.val, A y) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact A.mem_graph y
    · intro w member
      change WithLp.ofLp w ∈ A.graph at member
      obtain ⟨z, hz, hA⟩ := A.mem_graph_iff.mp member
      have same : w = WithLp.toLp 2 (z.val, A z) := by
        apply (WithLp.linearEquiv 2 ℂ (H × F)).injective
        exact Prod.ext hz.symm hA.symm
      rw [same, lift_apply, inner_sub_left, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only [inner_zero_left, add_zero]
      have relation := weak z
      rw [inner_sub_left] at relation
      linear_combination relation
  exact (congrArg (fun w : Product (H := H) (F := F) => w.fst) projected).symm.trans
    (resolvent_apply A closed x).symm

variable (U : H ≃ₗᵢ[ℂ] H) (inside : ∀ x, U x ∈ A.domain ↔ x ∈ A.domain)

def formPoint (x : A.domain) : A.domain := ⟨U x.val, (inside x.val).mpr x.property⟩

variable (preserves : ∀ x y : A.domain,
  inner ℂ (A (formPoint A U inside x)) (A (formPoint A U inside y)) = inner ℂ (A x) (A y))

include preserves in
theorem resolvent_commutes (x : H) : U (resolvent A closed x) = resolvent A closed (U x) := by
  apply solution_unique A closed (U x) (formPoint A U inside (solution A closed x))
  intro y
  let z : A.domain := ⟨U.symm y.val, (inside (U.symm y.val)).mp (by simp)⟩
  have recover : formPoint A U inside z = y := Subtype.ext (U.apply_symm_apply y.val)
  have source := variational A closed x z
  rw [← recover]
  change inner ℂ (U x - U (resolvent A closed x)) (U z.val) = _
  rw [← map_sub, U.inner_map_map, preserves]
  exact source

end
end SaturationMonoid.Quantum.Forms.Graph.Symmetry
