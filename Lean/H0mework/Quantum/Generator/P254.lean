import H0mework.Quantum.Generator.P253

/-!
# Proposition 254: self-adjoint Hamiltonian polarity certificate

P251 packages the Hamiltonian normal-form bridge once a flow has already been
certified to have generator `-i • H`.  P253 records the Hilbert-space
star-unitary laws forced by the bundled isometric time-slice type.

This file adds the missing star-algebra polarity on the Hamiltonian side: if
`H` is self-adjoint, then the generator candidate `-i • H` is skew-adjoint.
It also packages the conditional self-adjoint Hamiltonian flow certificate that
combines:

* Hamiltonian normal form;
* self-adjointness of `H`;
* skew-adjointness of `-i • H`;
* star-unitarity of the bundled time slices.

Boundary: this is still an algebraic polarity theorem.  It does not prove
Stone's theorem, derive strong continuity from an arbitrary unitary family,
construct `H` from a flow, prove that an arbitrary Hamiltonian is self-adjoint,
or establish full Schrödinger evolution for an arbitrary physical system.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Self-adjoint Hamiltonians have skew-adjoint `-i` generators -/

/-- A self-adjoint Hamiltonian operator has skew-adjoint generator candidate
`-i • H`. -/
theorem selfAdjointHamiltonian_skewGenerator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    (-Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E) := by
  have hI : Complex.I • H ∈ skewAdjoint (E →L[ℂ] E) :=
    hH.I_smul_mem_skewAdjoint
  have hneg : -(Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E) :=
    (skewAdjoint (E →L[ℂ] E)).neg_mem hI
  simpa [neg_smul] using hneg

/-- Real scalar rescaling preserves self-adjointness of a Hamiltonian operator. -/
theorem selfAdjointHamiltonian_real_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (omega : ℝ) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint ((omega : ℂ) • H) := by
  have homega : IsSelfAdjoint (omega : ℂ) := by
    simp [IsSelfAdjoint]
  exact homega.smul hH

/-- After real time-rescaling, the rescaled Hamiltonian still yields a
skew-adjoint `-i` generator candidate. -/
theorem selfAdjointHamiltonian_timeRescale_skewGenerator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (omega : ℝ) (hH : IsSelfAdjoint H) :
    (-Complex.I • ((omega : ℂ) • H)) ∈
      skewAdjoint (E →L[ℂ] E) :=
  selfAdjointHamiltonian_skewGenerator
    ((omega : ℂ) • H)
    (selfAdjointHamiltonian_real_smul H omega hH)

/-! ## Bundled Hamiltonian-side certificates -/

/-- The Hamiltonian-side algebraic certificate: `H` is self-adjoint and
therefore `-i • H` is skew-adjoint. -/
structure SelfAdjointHamiltonianGeneratorCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) : Prop where
  self_adjoint : IsSelfAdjoint H
  skew_generator :
    (-Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E)

/-- Bundle the Hamiltonian-side polarity certificate from self-adjointness. -/
theorem selfAdjointHamiltonianGeneratorCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    SelfAdjointHamiltonianGeneratorCertificate E H where
  self_adjoint := hH
  skew_generator := selfAdjointHamiltonian_skewGenerator H hH

/-- Real rescaling preserves the Hamiltonian-side polarity certificate. -/
theorem SelfAdjointHamiltonianGeneratorCertificate.timeRescale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E)
    (hH : SelfAdjointHamiltonianGeneratorCertificate E H)
    (omega : ℝ) :
    SelfAdjointHamiltonianGeneratorCertificate E ((omega : ℂ) • H) where
  self_adjoint :=
    selfAdjointHamiltonian_real_smul H omega hH.self_adjoint
  skew_generator :=
    selfAdjointHamiltonian_timeRescale_skewGenerator
      H omega hH.self_adjoint

/-! ## Conditional self-adjoint Hamiltonian flow certificate -/

/-- A conditional self-adjoint Hamiltonian flow certificate.

The analytic orbit equation still comes from `HamiltonianNormalFormFlowCertificate`.
This object only adds the star-algebra polarity of `H` and the star-unitary
time-slice laws forced by the bundled isometric flow type. -/
structure SelfAdjointHamiltonianFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E) : Prop where
  normal_form : HamiltonianNormalFormFlowCertificate E U H
  hamiltonian_polarity :
    SelfAdjointHamiltonianGeneratorCertificate E H
  star_unitary_flow : StarUnitaryFlowCertificate E U

/-- Bundle a self-adjoint Hamiltonian flow certificate from an existing
Hamiltonian normal-form certificate plus self-adjointness of `H`. -/
theorem selfAdjointHamiltonianFlowCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : HamiltonianNormalFormFlowCertificate E U H)
    (hH : IsSelfAdjoint H) :
    SelfAdjointHamiltonianFlowCertificate E U H where
  normal_form := hU
  hamiltonian_polarity :=
    selfAdjointHamiltonianGeneratorCertificate H hH
  star_unitary_flow := starUnitaryFlowCertificate U

/-- Forget the bundled self-adjoint Hamiltonian flow certificate back to the
Hamiltonian normal-form certificate. -/
theorem SelfAdjointHamiltonianFlowCertificate.toHamiltonianNormalForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : SelfAdjointHamiltonianFlowCertificate E U H) :
    HamiltonianNormalFormFlowCertificate E U H :=
  hU.normal_form

/-- Extract the skew-adjoint generator polarity from a bundled self-adjoint
Hamiltonian flow certificate. -/
theorem SelfAdjointHamiltonianFlowCertificate.skewGenerator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : SelfAdjointHamiltonianFlowCertificate E U H) :
    (-Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E) :=
  hU.hamiltonian_polarity.skew_generator

/-- Extract the star-unitary time-slice laws from a bundled self-adjoint
Hamiltonian flow certificate. -/
theorem SelfAdjointHamiltonianFlowCertificate.toStarUnitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : SelfAdjointHamiltonianFlowCertificate E U H) :
    StarUnitaryFlowCertificate E U :=
  hU.star_unitary_flow

/-- Time rescaling preserves the bundled self-adjoint Hamiltonian flow
certificate, sending `H` to `(omega : ℂ) • H`. -/
theorem SelfAdjointHamiltonianFlowCertificate.timeRescale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (hU : SelfAdjointHamiltonianFlowCertificate E U H)
    (omega : ℝ) :
    SelfAdjointHamiltonianFlowCertificate E
      (timeRescaledFlowHom (E := E) U omega)
      ((omega : ℂ) • H) where
  normal_form :=
    hamiltonianNormalFormFlowCertificate_timeRescale
      U H hU.normal_form omega
  hamiltonian_polarity :=
    hU.hamiltonian_polarity.timeRescale H omega
  star_unitary_flow :=
    starUnitaryFlowCertificate_timeRescale U omega

/-! ## Scalar sign-convention instance -/

/-- The scalar Schrödinger sign-convention slice is a self-adjoint Hamiltonian
flow certificate for `H = omega • Id`. -/
theorem schrodingerScalarPhaseFlow_selfAdjointHamiltonianFlowCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (omega : ℝ) :
    SelfAdjointHamiltonianFlowCertificate E
      (schrodingerScalarPhaseFlowHom (E := E) omega)
      ((omega : ℂ) • (1 : E →L[ℂ] E)) := by
  have hOne : IsSelfAdjoint (1 : E →L[ℂ] E) := by
    simp
  exact selfAdjointHamiltonianFlowCertificate
    (schrodingerScalarPhaseFlowHom (E := E) omega)
    ((omega : ℂ) • (1 : E →L[ℂ] E))
    (schrodingerScalarPhaseFlow_hamiltonianNormalFormCertificate
      (E := E) omega)
    (selfAdjointHamiltonian_real_smul
      (1 : E →L[ℂ] E) omega hOne)


end

end AffineRelaxation
end SaturationMonoid
