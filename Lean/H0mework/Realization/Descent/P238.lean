import H0mework.Realization.RelaxationAlgebra.P237

/-!
# Proposition 238: bundled scalar phase-flow group law

P237 bundles each unit-norm zero-target scalar phase slice as a linear
isometric automorphism `E ≃ₗᵢ[ℂ] E`.

This file upgrades the scalar `exp(i t)` flow from pointwise action equalities
to object-level group equalities in the bundled automorphism group.

Boundary: this is still the scalar `U(1)` phase-flow skeleton.  It does not
prove a general Hilbert-space unitary group, a Hamiltonian generator theorem,
Schrödinger evolution, tensor geometry, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Bundled object-level flow laws -/

/-- The bundled scalar phase flow is identity at time zero. -/
theorem unitComplexPhaseLinearIsometryEquiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    unitComplexPhaseLinearIsometryEquiv (E := E) 0 = 1 := by
  ext x
  simpa [unitComplexPhase_zero] using (phase_relaxModule_one (x := x))

/-- The bundled scalar phase flow maps time addition to composition.

Mathlib's group law on `E ≃ₗᵢ[ℂ] E` is composition: `(e * e') x = e (e' x)`,
so the right-hand side is "first time `t`, then time `s`". -/
theorem unitComplexPhaseLinearIsometryEquiv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t s : ℝ) :
    unitComplexPhaseLinearIsometryEquiv (E := E) (t + s) =
      unitComplexPhaseLinearIsometryEquiv (E := E) s *
        unitComplexPhaseLinearIsometryEquiv (E := E) t := by
  ext x
  simpa using
    (unitComplexPhaseLinearIsometryEquiv_apply_add (E := E) t s x).symm

/-- The bundled scalar phase flow is an abelian one-parameter family inside the
linear-isometry automorphism group. -/
theorem unitComplexPhaseLinearIsometryEquiv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t s : ℝ) :
    unitComplexPhaseLinearIsometryEquiv (E := E) t *
        unitComplexPhaseLinearIsometryEquiv (E := E) s =
      unitComplexPhaseLinearIsometryEquiv (E := E) s *
        unitComplexPhaseLinearIsometryEquiv (E := E) t := by
  rw [← unitComplexPhaseLinearIsometryEquiv_add (E := E) s t]
  rw [← unitComplexPhaseLinearIsometryEquiv_add (E := E) t s]
  rw [add_comm]


end AffineRelaxation
end SaturationMonoid
