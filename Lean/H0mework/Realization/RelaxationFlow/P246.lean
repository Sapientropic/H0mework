import H0mework.Realization.RelaxationFlow.P240

/-!
# Proposition 246: scalar phase-flow generator

P236-P240 prove that the concrete scalar phase family

`u(t) = exp(i t)`

forms a time-additive unit-norm phase flow, bundles to linear isometric
automorphisms, and has continuous point orbits.

This file proves the next analytic layer for the same scalar slice: every
point orbit is differentiable and solves the scalar generator equation

`dψ/dt = i • ψ(t)`.

Boundary: this is only the generator of the concrete scalar `U(1)` action
`t ↦ exp(i t)`.  It is not Stone's theorem, not a general Hilbert-space
unitary group theorem, not a Hamiltonian identification, not Schrödinger
evolution for arbitrary Hamiltonians, and not tensor/gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Scalar phase derivative -/

/-- The scalar phase `exp(i t)` has derivative `i * exp(i t)`. -/
theorem hasDerivAt_unitComplexPhase (t : ℝ) :
    HasDerivAt (fun τ : ℝ => unitComplexPhase τ)
      (Complex.I * unitComplexPhase t) t := by
  unfold unitComplexPhase
  have hlinear :
      HasDerivAt (fun τ : ℝ => Complex.I * (τ : ℂ)) Complex.I t := by
    have hof :
        HasDerivAt (fun τ : ℝ => (τ : ℂ)) (1 : ℂ) t := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id' t))
    simpa using (HasDerivAt.const_mul Complex.I hof)
  convert hlinear.cexp using 1
  ring

/-- Multiplication by the scalar phase gives point orbits satisfying
`dψ/dt = i • ψ(t)`. -/
theorem hasDerivAt_unitComplexPhase_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (x : E) :
    HasDerivAt (fun τ : ℝ => unitComplexPhase τ • x)
      (Complex.I • (unitComplexPhase t • x)) t := by
  simpa [smul_smul] using (hasDerivAt_unitComplexPhase t).smul_const x

/-! ## Bundled phase-flow orbit derivative -/

/-- The bundled scalar phase-flow automorphism has differentiable point orbits
with scalar generator `i`. -/
theorem hasDerivAt_unitComplexPhaseLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ => unitComplexPhaseLinearIsometryEquiv (E := E) τ x)
      (Complex.I • (unitComplexPhaseLinearIsometryEquiv (E := E) t x)) t := by
  simpa [unitComplexPhaseLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul] using
    (hasDerivAt_unitComplexPhase_smul (E := E) t x)

/-- The hom-packaged scalar phase-flow automorphism has differentiable point
orbits with scalar generator `i`. -/
theorem hasDerivAt_unitComplexPhaseFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd τ) x)
      (Complex.I •
        (unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd t) x)) t := by
  simpa [unitComplexPhaseFlowHom_apply] using
    (hasDerivAt_unitComplexPhaseLinearIsometryEquiv_apply (E := E) t x)

/-- A bundled certificate for the scalar phase-flow generator slice.

This certificate intentionally says "scalar generator" rather than
"Hamiltonian": it identifies the derivative of the concrete `exp(i t)` action,
but it does not construct a general self-adjoint generator. -/
structure ScalarPhaseFlowGeneratorCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop where
  phase_derivative :
    ∀ t : ℝ,
      HasDerivAt (fun τ : ℝ => unitComplexPhase τ)
        (Complex.I * unitComplexPhase t) t
  orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt (fun τ : ℝ => unitComplexPhase τ • x)
        (Complex.I • (unitComplexPhase t • x)) t
  bundled_orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ => unitComplexPhaseLinearIsometryEquiv (E := E) τ x)
        (Complex.I • (unitComplexPhaseLinearIsometryEquiv (E := E) t x)) t
  hom_orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ =>
          unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd τ) x)
        (Complex.I •
          (unitComplexPhaseFlowHom (E := E) (Multiplicative.ofAdd t) x)) t

/-- Complex normed-vector carriers supply the scalar phase-flow generator
certificate. -/
theorem scalarPhaseFlowGeneratorCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ScalarPhaseFlowGeneratorCertificate E where
  phase_derivative := hasDerivAt_unitComplexPhase
  orbit_derivative := hasDerivAt_unitComplexPhase_smul
  bundled_orbit_derivative := hasDerivAt_unitComplexPhaseLinearIsometryEquiv_apply
  hom_orbit_derivative := hasDerivAt_unitComplexPhaseFlowHom_apply


end

end AffineRelaxation
end SaturationMonoid
