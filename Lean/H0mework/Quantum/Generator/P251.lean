import H0mework.Quantum.Generator.P250

/-!
# Proposition 251: Hamiltonian normal-form certificate

P250 proves that any certified continuous-linear generator rescales correctly
under `t ↦ omega*t`.

This file packages the standard Schrödinger/Hamiltonian sign convention as a
certificate-relative theorem:

if a bundled flow has generator `-i • H`, then its point orbits satisfy the
normal-form algebra

`i • dψ/dt = H ψ`.

It also proves that time rescaling sends the Hamiltonian parameter `H` to
`omega • H`, and records the P248 scalar sign-convention slice as the
`H = omega • Id` instance.

Boundary: this still does not prove Stone's theorem, self-adjointness,
physical time selection, or that a concrete flow has generator `-i • H`.  It
only proves the normal-form algebra and its time-rescaling behavior once the
generator certificate has already been supplied.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Algebraic normal form for `-i • H` -/

/-- Multiplying a `-i` generated vector by `i` returns the original vector. -/
theorem complex_I_smul_neg_complex_I_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (y : E) :
    Complex.I • (-Complex.I • y) = y := by
  rw [smul_smul]
  have h : Complex.I * -Complex.I = (1 : ℂ) := by
    ring_nf
    norm_num [Complex.I_mul_I]
  rw [h, one_smul]

/-- The continuous-linear generator `-i • H` has Schrödinger normal form at
each carrier vector. -/
theorem complex_I_smul_hamiltonianGenerator_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : E →L[ℂ] E) (y : E) :
    Complex.I • ((-Complex.I • H) y) = H y := by
  simpa using complex_I_smul_neg_complex_I_smul (H y)

/-! ## Hamiltonian normal-form certificate -/

/-- A bundled one-parameter flow whose point orbits have generator `-i • H`,
with the scalar Schrödinger normal form recorded explicitly.

The certificate is intentionally conditional: it assumes the orbit derivative.
It does not construct `H` from `U`. -/
structure HamiltonianNormalFormFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E) : Prop where
  orbit_derivative :
    ∀ t : ℝ, ∀ x : E,
      HasDerivAt
        (fun τ : ℝ => U (Multiplicative.ofAdd τ) x)
        ((-Complex.I • H) (U (Multiplicative.ofAdd t) x)) t
  normal_form :
    ∀ t : ℝ, ∀ x : E,
      Complex.I •
        ((-Complex.I • H) (U (Multiplicative.ofAdd t) x)) =
      H (U (Multiplicative.ofAdd t) x)

/-- A linear-generator certificate with generator `-i • H` supplies the
Hamiltonian normal-form certificate. -/
theorem LinearGeneratorFlowCertificate.toHamiltonianNormalForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : LinearGeneratorFlowCertificate E U (-Complex.I • H)) :
    HamiltonianNormalFormFlowCertificate E U H where
  orbit_derivative := hU.orbit_derivative
  normal_form := by
    intro t x
    exact complex_I_smul_hamiltonianGenerator_apply H
      (U (Multiplicative.ofAdd t) x)

/-- Forget a Hamiltonian normal-form certificate back to its linear-generator
certificate. -/
theorem HamiltonianNormalFormFlowCertificate.toLinearGenerator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : HamiltonianNormalFormFlowCertificate E U H) :
    LinearGeneratorFlowCertificate E U (-Complex.I • H) where
  orbit_derivative := hU.orbit_derivative

/-! ## Time rescaling of Hamiltonian normal form -/

/-- Scaling a `-i • H` generator by a real time factor is the same as replacing
`H` by `omega • H`. -/
theorem timeRescale_hamiltonianGenerator_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : E →L[ℂ] E) (omega : ℝ) :
    ((omega : ℂ) • (-Complex.I • H)) =
      (-Complex.I • ((omega : ℂ) • H)) := by
  ext y
  change (omega : ℂ) • (-Complex.I • H y) =
    -Complex.I • ((omega : ℂ) • H y)
  rw [smul_smul, smul_smul]
  ring_nf

/-- Time rescaling preserves the Hamiltonian normal form and rescales the
Hamiltonian by the same real factor. -/
theorem hamiltonianNormalFormFlowCertificate_timeRescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : HamiltonianNormalFormFlowCertificate E U H)
    (omega : ℝ) :
    HamiltonianNormalFormFlowCertificate E
      (timeRescaledFlowHom (E := E) U omega) ((omega : ℂ) • H) where
  orbit_derivative := by
    intro t x
    have hlin :=
      linearGeneratorFlowCertificate_timeRescale
        U (-Complex.I • H)
        (HamiltonianNormalFormFlowCertificate.toLinearGenerator U H hU)
        omega
    let y :=
      timeRescaledFlowHom (E := E) U omega (Multiplicative.ofAdd t) x
    have hgen :
        (((omega : ℂ) • (-Complex.I • H)) y) =
          ((-Complex.I • ((omega : ℂ) • H)) y) := by
      rw [timeRescale_hamiltonianGenerator_eq H omega]
    change HasDerivAt
      (fun τ : ℝ =>
        timeRescaledFlowHom (E := E) U omega (Multiplicative.ofAdd τ) x)
      ((-Complex.I • ((omega : ℂ) • H)) y) t
    rw [← hgen]
    simpa [y] using hlin.orbit_derivative t x
  normal_form := by
    intro t x
    exact complex_I_smul_hamiltonianGenerator_apply ((omega : ℂ) • H)
      (timeRescaledFlowHom (E := E) U omega (Multiplicative.ofAdd t) x)

/-! ## P248 scalar sign-convention as the scalar-identity Hamiltonian case -/

/-- The scalar Schrödinger sign-convention slice is the Hamiltonian normal
form with Hamiltonian `omega • Id`. -/
theorem schrodingerScalarPhaseFlow_hamiltonianNormalFormCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    HamiltonianNormalFormFlowCertificate E
      (schrodingerScalarPhaseFlowHom (E := E) omega)
      ((omega : ℂ) • (1 : E →L[ℂ] E)) where
  orbit_derivative := by
    intro t x
    have h := hasDerivAt_schrodingerScalarPhaseFlowHom_apply
      (E := E) omega t x
    let y :=
      schrodingerScalarPhaseFlowHom
        (E := E) omega (Multiplicative.ofAdd t) x
    have hgen :
        -((omega : ℂ) * Complex.I) • y =
          ((-Complex.I • ((omega : ℂ) • (1 : E →L[ℂ] E))) y) := by
      change -((omega : ℂ) * Complex.I) • y =
        -Complex.I • ((omega : ℂ) • y)
      rw [smul_smul]
      ring_nf
    change HasDerivAt
      (fun τ : ℝ =>
        schrodingerScalarPhaseFlowHom
          (E := E) omega (Multiplicative.ofAdd τ) x)
      ((-Complex.I • ((omega : ℂ) • (1 : E →L[ℂ] E))) y) t
    rw [← hgen]
    simpa [y] using h
  normal_form := by
    intro t x
    exact complex_I_smul_hamiltonianGenerator_apply
      ((omega : ℂ) • (1 : E →L[ℂ] E))
      (schrodingerScalarPhaseFlowHom
        (E := E) omega (Multiplicative.ofAdd t) x)


end

end AffineRelaxation
end SaturationMonoid
