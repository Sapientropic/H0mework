import H0mework.Realization.RelaxationFlow.P252
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Proposition 253: Hilbert-space star-unitary slice certificate

P252 records the norm/distance/zero conservation forced by a flow valued in
bundled linear isometric automorphisms `E ≃ₗᵢ[ℂ] E`.

This file adds the Hilbert-space star-algebra face: when `E` is a complex
Hilbert carrier, every time slice, viewed as a continuous linear operator
`E →L[ℂ] E`, has adjoint equal to its inverse and is a unitary element of the
operator star monoid.

Boundary: this is still a time-slice theorem.  It does not prove Stone's
theorem, derive a self-adjoint generator, construct a Hamiltonian from the
flow, or show that an arbitrary physical system supplies such a flow.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Star-unitary laws for bundled isometric time slices -/

/-- The Hilbert-space star-unitary laws forced by a one-parameter flow valued
in bundled linear isometric automorphisms. -/
structure StarUnitaryFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) : Prop where
  adjoint_slice :
    ∀ t : ℝ,
      ContinuousLinearMap.adjoint
          (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
        ((U (Multiplicative.ofAdd t)).symm : E →L[ℂ] E)
  unitary_slice :
    ∀ t : ℝ,
      (U (Multiplicative.ofAdd t) : E →L[ℂ] E) ∈
        unitary (E →L[ℂ] E)
  star_mul_self_slice :
    ∀ t : ℝ,
      star (U (Multiplicative.ofAdd t) : E →L[ℂ] E) *
          (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
        1
  mul_star_self_slice :
    ∀ t : ℝ,
      (U (Multiplicative.ofAdd t) : E →L[ℂ] E) *
          star (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
        1

/-- Each bundled Hilbert-space isometric time slice has adjoint equal to its
inverse. -/
theorem isometricFlow_adjoint_slice_eq_symm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) :
    ContinuousLinearMap.adjoint
        (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
      ((U (Multiplicative.ofAdd t)).symm : E →L[ℂ] E) := by
  simp

/-- Each bundled Hilbert-space isometric time slice is a unitary element of the
operator star monoid. -/
theorem isometricFlow_unitary_slice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) :
    (U (Multiplicative.ofAdd t) : E →L[ℂ] E) ∈
      unitary (E →L[ℂ] E) := by
  rw [Unitary.mem_iff]
  constructor
  · ext x
    simp
  · ext x
    simp

/-- The left star-unitary equation for every bundled Hilbert-space isometric
time slice. -/
theorem isometricFlow_star_mul_self_slice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) :
    star (U (Multiplicative.ofAdd t) : E →L[ℂ] E) *
        (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
      1 := by
  exact Unitary.star_mul_self_of_mem (isometricFlow_unitary_slice U t)

/-- The right star-unitary equation for every bundled Hilbert-space isometric
time slice. -/
theorem isometricFlow_mul_star_self_slice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) :
    (U (Multiplicative.ofAdd t) : E →L[ℂ] E) *
        star (U (Multiplicative.ofAdd t) : E →L[ℂ] E) =
      1 := by
  exact Unitary.mul_star_self_of_mem (isometricFlow_unitary_slice U t)

/-- Bundle the Hilbert-space star-unitary laws for any flow valued in linear
isometric automorphisms. -/
theorem starUnitaryFlowCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) :
    StarUnitaryFlowCertificate E U where
  adjoint_slice := isometricFlow_adjoint_slice_eq_symm U
  unitary_slice := isometricFlow_unitary_slice U
  star_mul_self_slice := isometricFlow_star_mul_self_slice U
  mul_star_self_slice := isometricFlow_mul_star_self_slice U

/-! ## Stability under time rescaling and generator/Hamiltonian certificates -/

/-- Time-rescaled bundled Hilbert-space flows inherit the same star-unitary
time-slice laws. -/
theorem starUnitaryFlowCertificate_timeRescale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (omega : ℝ) :
    StarUnitaryFlowCertificate E
      (timeRescaledFlowHom (E := E) U omega) :=
  starUnitaryFlowCertificate
    (timeRescaledFlowHom (E := E) U omega)

/-- A continuous-linear-generator certificate carries the star-unitary laws of
its bundled Hilbert-space isometric flow. -/
theorem LinearGeneratorFlowCertificate.toStarUnitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (_hU : LinearGeneratorFlowCertificate E U A) :
    StarUnitaryFlowCertificate E U :=
  starUnitaryFlowCertificate U

/-- A Hamiltonian normal-form certificate carries the star-unitary laws of its
bundled Hilbert-space isometric flow. -/
theorem HamiltonianNormalFormFlowCertificate.toStarUnitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (_hU : HamiltonianNormalFormFlowCertificate E U H) :
    StarUnitaryFlowCertificate E U :=
  starUnitaryFlowCertificate U

/-- The scalar Schrödinger sign-convention slice is star-unitary on any complex
Hilbert carrier because it is a bundled linear isometric flow. -/
theorem schrodingerScalarPhaseFlow_starUnitaryCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (omega : ℝ) :
    StarUnitaryFlowCertificate E
      (schrodingerScalarPhaseFlowHom (E := E) omega) :=
  starUnitaryFlowCertificate
    (schrodingerScalarPhaseFlowHom (E := E) omega)


end

end AffineRelaxation
end SaturationMonoid
