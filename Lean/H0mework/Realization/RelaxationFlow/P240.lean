import H0mework.Realization.Descent.P239

/-!
# Proposition 240: pointwise continuity of the scalar phase flow

P239 packages the scalar `exp(i t)` phase flow as a monoid hom

`Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E`.

This file proves the next analytic layer: for every carrier point `x`, the
orbit `t ↦ U(t) x` is continuous.  This is the scalar strong-continuity
skeleton for this specific `U(1)` action.

Boundary: this is still only the scalar phase action.  It does not prove
Stone's theorem, identify a Hamiltonian generator, derive Schrödinger
evolution, or construct tensor/gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Scalar phase continuity -/

/-- The concrete scalar phase family `t ↦ exp(i t)` is continuous. -/
theorem continuous_unitComplexPhase :
    Continuous unitComplexPhase := by
  unfold unitComplexPhase
  exact (continuous_const.mul Complex.continuous_ofReal).cexp

/-- For every carrier point `x`, scalar phase multiplication by `exp(i t)` is
continuous in time. -/
theorem continuous_unitComplexPhase_smul
    {E : Type*} [TopologicalSpace E] [SMul ℂ E] [ContinuousSMul ℂ E]
    (x : E) :
    Continuous (fun t : ℝ => unitComplexPhase t • x) :=
  continuous_unitComplexPhase.smul continuous_const

/-! ## Bundled flow continuity, pointwise on carrier states -/

/-- The bundled scalar phase-flow automorphism has continuous point orbits. -/
theorem continuous_unitComplexPhaseLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) :
    Continuous (fun t : ℝ => unitComplexPhaseLinearIsometryEquiv (E := E) t x) := by
  simpa [unitComplexPhaseLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul] using
    (continuous_unitComplexPhase_smul (E := E) x)

/-- The hom-packaged scalar phase flow has continuous point orbits. -/
theorem continuous_unitComplexPhaseFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) :
    Continuous
      (fun t : ℝ =>
        unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd t) x) := by
  simpa [unitComplexPhaseFlowHom_apply] using
    (continuous_unitComplexPhaseLinearIsometryEquiv_apply (E := E) x)

/-- A small named certificate for the scalar phase flow's pointwise continuity.

This is intentionally pointwise.  It should not be read as Stone's theorem or a
Hamiltonian-generator theorem. -/
structure ScalarPhaseFlowPointwiseContinuousCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop where
  continuous_orbit :
    ∀ x : E,
      Continuous
        (fun t : ℝ =>
          unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd t) x)

/-- The concrete scalar phase flow supplies the pointwise-continuity
certificate. -/
theorem scalarPhaseFlowPointwiseContinuousCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ScalarPhaseFlowPointwiseContinuousCertificate E where
  continuous_orbit := continuous_unitComplexPhaseFlowHom_apply


end AffineRelaxation
end SaturationMonoid
