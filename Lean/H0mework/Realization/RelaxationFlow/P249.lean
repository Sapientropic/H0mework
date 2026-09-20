import H0mework.Quantum.Generator.P248

/-!
# Proposition 249: abstract scalar-generator time rescaling

P246-P248 prove generator equations for concrete scalar `U(1)` phase flows.
This file abstracts one reusable bridge from those examples:

if a one-parameter bundled flow has scalar generator `gamma`, then the
time-rescaled flow `t ↦ U(omega * t)` has scalar generator `omega * gamma`.

This is a genuine step away from a single scalar example, but the boundary is
still important.  The theorem assumes a scalar-generator orbit derivative as an
input certificate.  It does not prove Stone's theorem, construct a Hamiltonian,
prove self-adjointness, or derive general Schrödinger evolution.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Abstract scalar-generator flow certificate -/

/-- A one-parameter bundled flow whose point orbits have scalar generator
`gamma`.

The flow itself is already a monoid hom
`Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E`.  This certificate adds the analytic orbit
equation. -/
structure ScalarGeneratorFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (gamma : ℂ) : Prop where
  orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ => U (Multiplicative.ofAdd τ) x)
        (gamma • (U (Multiplicative.ofAdd t) x)) t

/-! ## Time-rescaled bundled flows -/

/-- Rescale a bundled one-parameter flow by a real time factor `omega`.

If `U(t+s)=U(t)U(s)`, then `t ↦ U(omega*t)` is again a bundled flow. -/
noncomputable def timeRescaledFlowHom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (omega : ℝ) :
    Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E where
  toFun t := U (Multiplicative.ofAdd (omega * t.toAdd))
  map_one' := by
    simp
  map_mul' := by
    intro t s
    have hmul :
        Multiplicative.ofAdd (omega * (t.toAdd + s.toAdd)) =
          Multiplicative.ofAdd (omega * t.toAdd) *
            Multiplicative.ofAdd (omega * s.toAdd) := by
      rw [← ofAdd_add]
      congr 1
      ring
    change U (Multiplicative.ofAdd (omega * (t.toAdd + s.toAdd))) =
      U (Multiplicative.ofAdd (omega * t.toAdd)) *
        U (Multiplicative.ofAdd (omega * s.toAdd))
    rw [hmul]
    exact U.map_mul _ _

@[simp]
theorem timeRescaledFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (omega : ℝ)
    (t : Multiplicative ℝ) :
    timeRescaledFlowHom (E := E) U omega t =
      U (Multiplicative.ofAdd (omega * t.toAdd)) := rfl

/-! ## Generator rescaling -/

/-- If `U` has scalar generator `gamma`, then `t ↦ U(omega*t)` has scalar
generator `omega * gamma`. -/
theorem hasDerivAt_timeRescaledFlowHom_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (gamma : ℂ)
    (hU : ScalarGeneratorFlowCertificate E U gamma)
    (omega t : ℝ) (x : E) :
    HasDerivAt
      (fun τ : ℝ =>
        timeRescaledFlowHom (E := E) U omega (Multiplicative.ofAdd τ) x)
      (((omega : ℂ) * gamma) •
        (timeRescaledFlowHom (E := E) U omega
          (Multiplicative.ofAdd t) x)) t := by
  have harg : HasDerivAt (fun τ : ℝ => omega * τ) omega t := by
    simpa using (hasDerivAt_id' t).const_mul omega
  have horbit :=
    HasDerivAt.scomp t
      (hU.orbit_derivative (omega * t) x) harg
  let y := U (Multiplicative.ofAdd (omega * t)) x
  have hscale :
      ((omega : ℂ) * gamma) • y = omega • gamma • y := by
    calc
      ((omega : ℂ) * gamma) • y = (omega • gamma : ℂ) • y := by
        rw [Complex.real_smul]
      _ = omega • gamma • y := by
        exact IsScalarTower.smul_assoc omega gamma y
  change HasDerivAt
    (fun τ : ℝ => U (Multiplicative.ofAdd (omega * τ)) x)
    (((omega : ℂ) * gamma) • y) t
  rw [hscale]
  simpa [Function.comp_def, y] using horbit

/-- Time rescaling preserves scalar-generator flow certificates, with generator
scaled by the same real factor. -/
theorem scalarGeneratorFlowCertificate_timeRescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (gamma : ℂ)
    (hU : ScalarGeneratorFlowCertificate E U gamma)
    (omega : ℝ) :
    ScalarGeneratorFlowCertificate E
      (timeRescaledFlowHom (E := E) U omega) ((omega : ℂ) * gamma) where
  orbit_derivative := hasDerivAt_timeRescaledFlowHom_apply U gamma hU omega

/-! ## Concrete scalar phase flow as an instance of the abstract bridge -/

/-- The concrete scalar phase flow has scalar generator `i` in the abstract
certificate format. -/
theorem unitComplexPhaseFlow_scalarGeneratorCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ScalarGeneratorFlowCertificate E
      (unitComplexPhaseFlowHom (E := E)) Complex.I where
  orbit_derivative := hasDerivAt_unitComplexPhaseFlowHom_apply

/-- The fixed-rate scalar phase-flow certificate is the abstract rescaling
theorem applied to the concrete scalar phase flow. -/
theorem unitComplexPhaseFlow_timeRescaleCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    ScalarGeneratorFlowCertificate E
      (timeRescaledFlowHom (E := E)
        (unitComplexPhaseFlowHom (E := E)) omega)
      ((omega : ℂ) * Complex.I) :=
  scalarGeneratorFlowCertificate_timeRescale
    (unitComplexPhaseFlowHom (E := E)) Complex.I
    (unitComplexPhaseFlow_scalarGeneratorCertificate (E := E)) omega


end

end AffineRelaxation
end SaturationMonoid
