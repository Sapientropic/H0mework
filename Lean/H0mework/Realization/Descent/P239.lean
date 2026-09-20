import H0mework.Realization.Descent.P238

/-!
# Proposition 239: scalar phase flow as a bundled monoid hom

P238 proves the object-level laws for the bundled scalar `exp(i t)` phase flow.
This file packages those laws as a single reusable Lean object:

`Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E`.

Boundary: this is still the scalar `U(1)` phase-flow skeleton.  It does not
prove strong continuity, Stone's theorem, Hamiltonian generators, Schrödinger
evolution, tensor geometry, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Bundled scalar phase-flow homomorphism -/

/-- The scalar `exp(i t)` phase flow as a monoid hom from additive time
(`Multiplicative ℝ`) into the linear-isometry automorphism group.

`Multiplicative ℝ` lets Lean see time addition as source multiplication. -/
noncomputable def unitComplexPhaseFlowHom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E where
  toFun t := unitComplexPhaseLinearIsometryEquiv (E := E) t.toAdd
  map_one' := by
    simpa using (unitComplexPhaseLinearIsometryEquiv_zero (E := E))
  map_mul' := by
    intro t s
    change unitComplexPhaseLinearIsometryEquiv (E := E) (t.toAdd + s.toAdd) =
      unitComplexPhaseLinearIsometryEquiv (E := E) t.toAdd *
        unitComplexPhaseLinearIsometryEquiv (E := E) s.toAdd
    rw [unitComplexPhaseLinearIsometryEquiv_add]
    exact unitComplexPhaseLinearIsometryEquiv_comm (E := E) s.toAdd t.toAdd

@[simp]
theorem unitComplexPhaseFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : Multiplicative ℝ) :
    unitComplexPhaseFlowHom (E := E) t =
      unitComplexPhaseLinearIsometryEquiv (E := E) t.toAdd := rfl

/-- The hom object reproduces the object-level scalar phase-flow law. -/
theorem unitComplexPhaseFlowHom_map_mul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t s : Multiplicative ℝ) (x : E) :
    unitComplexPhaseFlowHom (E := E) (t * s) x =
      (unitComplexPhaseFlowHom (E := E) t *
        unitComplexPhaseFlowHom (E := E) s) x := by
  simpa [unitComplexPhaseFlowHom, add_comm] using
    (unitComplexPhaseLinearIsometryEquiv_apply_add
      (E := E) s.toAdd t.toAdd x).symm


end AffineRelaxation
end SaturationMonoid
