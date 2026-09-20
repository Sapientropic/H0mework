import H0mework.Realization.RelaxationFlow.P247

/-!
# Proposition 248: Schrödinger-sign scalar phase slice

P247 proves the fixed-rate scalar phase generator for

`exp(i omega t)`.

This file records the common physics sign convention for the scalar slice:

`exp(-i omega t)`.

It proves the derivative

`dψ/dt = -(omega * i) • ψ(t)`

and the equivalent scalar Schrödinger-normal form

`i • dψ/dt = omega • ψ(t)`.

Boundary: this is only the scalar sign-convention slice.  It is not a general
Hilbert-space unitary theorem, not a Hamiltonian construction, not a
self-adjointness theorem, and not Schrödinger evolution for arbitrary
Hamiltonians.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Schrödinger-sign scalar phase -/

/-- The scalar phase with the common Schrödinger sign convention:
`exp(-i omega t)`. -/
noncomputable def schrodingerScalarPhase (omega t : ℝ) : ℂ :=
  unitComplexPhaseWithRate (-omega) t

/-- The Schrödinger-sign scalar phase as a fixed-rate hom. -/
noncomputable def schrodingerScalarPhaseFlowHom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E :=
  unitComplexPhaseWithRateFlowHom (E := E) (-omega)

@[simp]
theorem schrodingerScalarPhaseFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) (t : Multiplicative ℝ) :
    schrodingerScalarPhaseFlowHom (E := E) omega t =
      unitComplexPhaseWithRateFlowHom (E := E) (-omega) t := rfl

/-! ## Generator and scalar Schrödinger-normal form -/

/-- `exp(-i omega t)` has derivative
`-(omega * i) * exp(-i omega t)`. -/
theorem hasDerivAt_schrodingerScalarPhase (omega t : ℝ) :
    HasDerivAt (fun τ : ℝ => schrodingerScalarPhase omega τ)
      (-((omega : ℂ) * Complex.I) * schrodingerScalarPhase omega t) t := by
  unfold schrodingerScalarPhase
  simpa [neg_mul, mul_assoc] using
    (hasDerivAt_unitComplexPhaseWithRate (-omega) t)

/-- The hom-packaged Schrödinger-sign scalar phase-flow automorphism has
differentiable point orbits with generator `-(omega * i)`. -/
theorem hasDerivAt_schrodingerScalarPhaseFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        schrodingerScalarPhaseFlowHom
          (E := E) omega (Multiplicative.ofAdd τ) x)
      (-((omega : ℂ) * Complex.I) •
        (schrodingerScalarPhaseFlowHom
          (E := E) omega (Multiplicative.ofAdd t) x)) t := by
  unfold schrodingerScalarPhaseFlowHom
  simpa [neg_mul, mul_assoc] using
    (hasDerivAt_unitComplexPhaseWithRateFlowHom_apply (E := E) (-omega) t x)

/-- Multiplying the Schrödinger-sign scalar generator by `i` gives the rate
`omega`. -/
theorem complex_I_mul_schrodingerScalarGenerator (omega : ℝ) :
    Complex.I * -((omega : ℂ) * Complex.I) = (omega : ℂ) := by
  ring_nf
  norm_num [Complex.I_mul_I]

/-- Scalar Schrödinger-normal form for a carrier vector:
`i • (-(omega*i) • y) = omega • y`. -/
theorem complex_I_smul_schrodingerScalarGenerator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) (y : E) :
    Complex.I • (-((omega : ℂ) * Complex.I) • y) = (omega : ℂ) • y := by
  rw [smul_smul, complex_I_mul_schrodingerScalarGenerator]

/-- A bundled certificate for the scalar Schrödinger-sign phase slice.

The certificate contains both the derivative sign convention and the scalar
normal-form identity `i • dψ/dt = omega • ψ(t)`. -/
structure ScalarSchrodingerSignPhaseCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop where
  orbit_derivative :
    ∀ omega t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ =>
          schrodingerScalarPhaseFlowHom
            (E := E) omega (Multiplicative.ofAdd τ) x)
        (-((omega : ℂ) * Complex.I) •
          (schrodingerScalarPhaseFlowHom
            (E := E) omega (Multiplicative.ofAdd t) x)) t
  scalar_normal_form :
    ∀ omega : ℝ, ∀ y : E,
      Complex.I • (-((omega : ℂ) * Complex.I) • y) = (omega : ℂ) • y

/-- Complex normed-vector carriers supply the scalar Schrödinger-sign phase
certificate. -/
theorem scalarSchrodingerSignPhaseCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ScalarSchrodingerSignPhaseCertificate E where
  orbit_derivative := hasDerivAt_schrodingerScalarPhaseFlowHom_apply
  scalar_normal_form := complex_I_smul_schrodingerScalarGenerator


end

end AffineRelaxation
end SaturationMonoid
