import H0mework.Realization.RelaxationFlow.P246

/-!
# Proposition 247: scalar phase-flow generator with rate

P246 proves the generator equation for the concrete dimensionless scalar phase
flow

`u(t) = exp(i t)`.

This file adds the first parameterized bridge:

`u_omega(t) = exp(i omega t)`.

It proves that a fixed real rate `omega` still gives a time-additive scalar
phase-flow hom, and that each point orbit solves

`dψ/dt = (omega * i) • ψ(t)`.

Boundary: `omega` is only a scalar rate parameter for the concrete `U(1)`
action.  This is not a physical energy identification, not a self-adjoint
Hamiltonian theorem, not Stone's theorem, not general Schrödinger evolution,
and not tensor/gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Scalar phase with a fixed real rate -/

/-- The scalar phase family with fixed rate `omega`: `exp(i omega t)`. -/
noncomputable def unitComplexPhaseWithRate (omega t : ℝ) : ℂ :=
  unitComplexPhase (omega * t)

/-- `exp(i omega t)` has unit norm for every fixed real rate. -/
theorem unitComplexPhaseWithRate_norm (omega t : ℝ) :
    ‖unitComplexPhaseWithRate omega t‖ = 1 := by
  exact unitComplexPhase_norm (omega * t)

/-- `exp(i omega * 0) = 1`. -/
theorem unitComplexPhaseWithRate_zero (omega : ℝ) :
    unitComplexPhaseWithRate omega 0 = 1 := by
  simp [unitComplexPhaseWithRate, unitComplexPhase_zero]

/-- The fixed-rate scalar phase maps addition of times to multiplication of
phases. -/
theorem unitComplexPhaseWithRate_add (omega t s : ℝ) :
    unitComplexPhaseWithRate omega (t + s) =
      unitComplexPhaseWithRate omega t * unitComplexPhaseWithRate omega s := by
  unfold unitComplexPhaseWithRate
  rw [show omega * (t + s) = omega * t + omega * s by ring]
  exact unitComplexPhase_add (omega * t) (omega * s)

/-! ## Bundled fixed-rate scalar phase-flow -/

/-- A fixed-rate scalar phase as a bundled linear isometric automorphism. -/
noncomputable def unitComplexPhaseWithRateLinearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) :
    E ≃ₗᵢ[ℂ] E :=
  unitComplexPhaseLinearIsometryEquiv (E := E) (omega * t)

@[simp]
theorem unitComplexPhaseWithRateLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) (x : E) :
    unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega t x =
      relaxModule (0 : E) (1 - unitComplexPhaseWithRate omega t) x := rfl

/-- The fixed-rate bundled scalar phase flow is identity at time zero. -/
theorem unitComplexPhaseWithRateLinearIsometryEquiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega 0 = 1 := by
  simp [unitComplexPhaseWithRateLinearIsometryEquiv,
    unitComplexPhaseLinearIsometryEquiv_zero]

/-- A fixed-rate bundled scalar phase flow maps time addition to composition. -/
theorem unitComplexPhaseWithRateLinearIsometryEquiv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t s : ℝ) :
    unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega (t + s) =
      unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega s *
        unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega t := by
  unfold unitComplexPhaseWithRateLinearIsometryEquiv
  rw [show omega * (t + s) = omega * t + omega * s by ring]
  exact unitComplexPhaseLinearIsometryEquiv_add
    (E := E) (omega * t) (omega * s)

/-- The fixed-rate scalar phase flow as a monoid hom from additive time
(`Multiplicative ℝ`) into the bundled automorphism group. -/
noncomputable def unitComplexPhaseWithRateFlowHom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E where
  toFun t := unitComplexPhaseWithRateLinearIsometryEquiv
    (E := E) omega t.toAdd
  map_one' := unitComplexPhaseWithRateLinearIsometryEquiv_zero
    (E := E) omega
  map_mul' := by
    intro t s
    change unitComplexPhaseWithRateLinearIsometryEquiv
        (E := E) omega (t.toAdd + s.toAdd) =
      unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega t.toAdd *
        unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega s.toAdd
    rw [unitComplexPhaseWithRateLinearIsometryEquiv_add]
    exact unitComplexPhaseLinearIsometryEquiv_comm
      (E := E) (omega * s.toAdd) (omega * t.toAdd)

@[simp]
theorem unitComplexPhaseWithRateFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) (t : Multiplicative ℝ) :
    unitComplexPhaseWithRateFlowHom (E := E) omega t =
      unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega t.toAdd := rfl

/-! ## Fixed-rate scalar generator -/

/-- The fixed-rate scalar phase has derivative
`(omega * i) * exp(i omega t)`. -/
theorem hasDerivAt_unitComplexPhaseWithRate (omega t : ℝ) :
    HasDerivAt (fun τ : ℝ => unitComplexPhaseWithRate omega τ)
      (((omega : ℂ) * Complex.I) * unitComplexPhaseWithRate omega t) t := by
  unfold unitComplexPhaseWithRate
  have harg : HasDerivAt (fun τ : ℝ => omega * τ) omega t := by
    simpa using (hasDerivAt_id' t).const_mul omega
  simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm, smul_eq_mul] using
    (HasDerivAt.scomp t (hasDerivAt_unitComplexPhase (omega * t)) harg)

/-- Fixed-rate scalar phase multiplication gives point orbits satisfying
`dψ/dt = (omega * i) • ψ(t)`. -/
theorem hasDerivAt_unitComplexPhaseWithRate_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) (x : E) :
    HasDerivAt (fun τ : ℝ => unitComplexPhaseWithRate omega τ • x)
      (((omega : ℂ) * Complex.I) •
        (unitComplexPhaseWithRate omega t • x)) t := by
  simpa [smul_smul] using
    (hasDerivAt_unitComplexPhaseWithRate omega t).smul_const x

/-- The bundled fixed-rate scalar phase-flow automorphism has differentiable
point orbits with scalar generator `omega * i`. -/
theorem hasDerivAt_unitComplexPhaseWithRateLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega τ x)
      (((omega : ℂ) * Complex.I) •
        (unitComplexPhaseWithRateLinearIsometryEquiv (E := E) omega t x)) t := by
  simpa [unitComplexPhaseWithRateLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul] using
    (hasDerivAt_unitComplexPhaseWithRate_smul (E := E) omega t x)

/-- The hom-packaged fixed-rate scalar phase-flow automorphism has
differentiable point orbits with scalar generator `omega * i`. -/
theorem hasDerivAt_unitComplexPhaseWithRateFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        unitComplexPhaseWithRateFlowHom
          (E := E) omega (Multiplicative.ofAdd τ) x)
      (((omega : ℂ) * Complex.I) •
        (unitComplexPhaseWithRateFlowHom
          (E := E) omega (Multiplicative.ofAdd t) x)) t := by
  simpa [unitComplexPhaseWithRateFlowHom_apply] using
    (hasDerivAt_unitComplexPhaseWithRateLinearIsometryEquiv_apply
      (E := E) omega t x)

/-- A bundled certificate for the fixed-rate scalar phase-flow generator.

This says only that the concrete scalar `U(1)` action with real rate `omega`
has the expected scalar generator.  It does not identify `omega` with a
physical energy or construct a Hamiltonian. -/
structure ScalarPhaseFlowWithRateGeneratorCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop where
  phase_derivative :
    ∀ omega t : ℝ,
      HasDerivAt (fun τ : ℝ => unitComplexPhaseWithRate omega τ)
        (((omega : ℂ) * Complex.I) * unitComplexPhaseWithRate omega t) t
  hom_orbit_derivative :
    ∀ omega t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ =>
          unitComplexPhaseWithRateFlowHom
            (E := E) omega (Multiplicative.ofAdd τ) x)
        (((omega : ℂ) * Complex.I) •
          (unitComplexPhaseWithRateFlowHom
            (E := E) omega (Multiplicative.ofAdd t) x)) t

/-- Complex normed-vector carriers supply the fixed-rate scalar phase-flow
generator certificate. -/
theorem scalarPhaseFlowWithRateGeneratorCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ScalarPhaseFlowWithRateGeneratorCertificate E where
  phase_derivative := hasDerivAt_unitComplexPhaseWithRate
  hom_orbit_derivative := hasDerivAt_unitComplexPhaseWithRateFlowHom_apply


end

end AffineRelaxation
end SaturationMonoid
