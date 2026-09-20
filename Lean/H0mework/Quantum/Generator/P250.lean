import H0mework.Realization.RelaxationFlow.P249

/-!
# Proposition 250: continuous-linear generator time rescaling

P249 proves the time-rescaling bridge for scalar generators:

`d/dt U(t)x = gamma • U(t)x`.

This file proves the corresponding bridge for an arbitrary continuous linear
generator certificate:

`d/dt U(t)x = A (U(t)x)`.

If that certificate is available, then the time-rescaled flow `t ↦ U(omega*t)`
has generator `(omega : ℂ) • A`.

Boundary: this still assumes the orbit derivative certificate.  It does not
prove Stone's theorem, construct a Hamiltonian, prove self-adjointness, or
derive Schrödinger evolution.  It only proves that once a continuous-linear
generator has been certified, real time-rescaling multiplies that generator by
the same rate.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Abstract continuous-linear generator flow certificate -/

/-- A bundled one-parameter flow whose point orbits have continuous-linear
generator `A`.

The flow itself is already a monoid hom
`Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E`.  This certificate adds the analytic orbit
equation. -/
structure LinearGeneratorFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) : Prop where
  orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ => U (Multiplicative.ofAdd τ) x)
        (A (U (Multiplicative.ofAdd t) x)) t

/-! ## Generator rescaling -/

/-- If `U` has continuous-linear generator `A`, then `t ↦ U(omega*t)` has
generator `(omega : ℂ) • A`. -/
theorem hasDerivAt_timeRescaledFlowHom_apply_linearGenerator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (hU : LinearGeneratorFlowCertificate E U A)
    (omega t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        timeRescaledFlowHom (E := E) U omega (Multiplicative.ofAdd τ) x)
      (((omega : ℂ) • A)
        (timeRescaledFlowHom (E := E) U omega
          (Multiplicative.ofAdd t) x)) t := by
  have harg : HasDerivAt (fun τ : ℝ => omega * τ) omega t := by
    simpa using (hasDerivAt_id' t).const_mul omega
  have horbit :=
    HasDerivAt.scomp t
      (hU.orbit_derivative (omega * t) x) harg
  let y := U (Multiplicative.ofAdd (omega * t)) x
  have hscale : omega • A y = (((omega : ℂ) • A) y) := by
    simp
  change HasDerivAt
    (fun τ : ℝ => U (Multiplicative.ofAdd (omega * τ)) x)
    ((((omega : ℂ) • A) y)) t
  rw [← hscale]
  simpa [Function.comp_def, y] using horbit

/-- Time rescaling preserves continuous-linear-generator flow certificates,
with generator scaled by the same real factor. -/
theorem linearGeneratorFlowCertificate_timeRescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (hU : LinearGeneratorFlowCertificate E U A)
    (omega : ℝ) :
    LinearGeneratorFlowCertificate E
      (timeRescaledFlowHom (E := E) U omega) ((omega : ℂ) • A) where
  orbit_derivative :=
    hasDerivAt_timeRescaledFlowHom_apply_linearGenerator U A hU omega

/-! ## Scalar generators as continuous-linear generators -/

/-- A scalar-generator certificate induces a continuous-linear-generator
certificate for the scalar multiple of the identity. -/
theorem scalarGeneratorFlowCertificate.toLinearGenerator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (gamma : ℂ)
    (hU : ScalarGeneratorFlowCertificate E U gamma) :
    LinearGeneratorFlowCertificate E U (gamma • (1 : E →L[ℂ] E)) where
  orbit_derivative := by
    intro t x
    simpa using hU.orbit_derivative t x

/-- P249's scalar bridge is the scalar-identity instance of the continuous
linear generator bridge. -/
theorem unitComplexPhaseFlow_linearGeneratorTimeRescaleCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    LinearGeneratorFlowCertificate E
      (timeRescaledFlowHom (E := E)
        (unitComplexPhaseFlowHom (E := E)) omega)
      ((omega : ℂ) • (Complex.I • (1 : E →L[ℂ] E))) :=
  linearGeneratorFlowCertificate_timeRescale
    (unitComplexPhaseFlowHom (E := E))
    (Complex.I • (1 : E →L[ℂ] E))
    (scalarGeneratorFlowCertificate.toLinearGenerator
      (unitComplexPhaseFlowHom (E := E)) Complex.I
      (unitComplexPhaseFlow_scalarGeneratorCertificate (E := E)))
    omega


end

end AffineRelaxation
end SaturationMonoid
