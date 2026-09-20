import H0mework.Quantum.Generator.P486
import H0mework.Quantum.Generator.P257

/-!
# Proposition 487: carrier-produced bounded Hamiltonian operators

P486 introduced the missing producer gate for scalar Hamiltonian scales:
before carrier growth may be read as Hamiltonian-scale growth, a certificate
must say that the scale is faithfully produced by the sampled inverse carrier.

This file lifts that gate from the scalar identity Hamiltonian `omega • Id` to
an arbitrary bounded self-adjoint base Hamiltonian `H₀`.

The construction is deliberately conservative:

* the base operator `H₀ : E →L[ℂ] E` is supplied as data;
* self-adjointness of `H₀` is supplied as data;
* the produced Hamiltonian sequence must be exactly
  `H_N = (scale N : ℂ) • H₀`;
* the scale must be exactly the sampled inverse-carrier scale from P486.

Under those hypotheses, every produced `H_N` is self-adjoint, has the bounded
exponential unitary-flow certificate, and has the bounded Schrödinger normal
form.  The carrier supplies the closed-form and divergence of the scalar
coefficient; it does not construct `H₀` or identify a concrete physical
Hamiltonian without this producer certificate.
-/

noncomputable section

open Filter

namespace SaturationMonoid
namespace AffineRelaxation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Bounded Hamiltonian producer -/

/-- A bounded self-adjoint Hamiltonian sequence whose scalar coefficient is
faithfully produced by the sampled inverse saturation carrier. -/
structure SampledInverseBoundedHamiltonianProducer
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (lambda step : ℝ) where
  baseHamiltonian : E →L[ℂ] E
  base_self_adjoint : IsSelfAdjoint baseHamiltonian
  scale : ℕ -> ℝ
  carrier_scale :
    ∀ N : ℕ, scale N = sampledInverseCarrierScale lambda step N
  hamiltonian : ℕ -> E →L[ℂ] E
  hamiltonian_scale :
    ∀ N : ℕ, hamiltonian N = ((scale N : ℂ) • baseHamiltonian)

/-- The canonical producer from a supplied bounded self-adjoint base
Hamiltonian. -/
def canonicalSampledInverseBoundedHamiltonianProducer
    (H₀ : E →L[ℂ] E) (hH₀ : IsSelfAdjoint H₀)
    (lambda step : ℝ) :
    SampledInverseBoundedHamiltonianProducer E lambda step where
  baseHamiltonian := H₀
  base_self_adjoint := hH₀
  scale := sampledInverseCarrierScale lambda step
  carrier_scale := by
    intro N
    rfl
  hamiltonian := fun N => ((sampledInverseCarrierScale lambda step N : ℂ) • H₀)
  hamiltonian_scale := by
    intro N
    rfl

/-- THEOREM 1: every bounded Hamiltonian producer forgets to the scalar
Hamiltonian-scale producer from P486. -/
def SampledInverseBoundedHamiltonianProducer.toScalarScaleProducer
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step) :
    SampledInverseHamiltonianScaleProducer E lambda step where
  scale := C.scale
  carrier_scale := C.carrier_scale
  scalar_hamiltonian_normal_form := by
    intro N
    exact
      schrodingerScalarPhaseFlow_hamiltonianNormalFormCertificate
        (E := E) (C.scale N)

/-- THEOREM 2: the produced scalar coefficient has the sampled inverse-carrier
closed form. -/
theorem SampledInverseBoundedHamiltonianProducer.scale_eq_exp_growth
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    C.scale N =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ :=
  (C.toScalarScaleProducer).scale_eq_exp_growth N

/-- THEOREM 3: the produced bounded Hamiltonian has the closed scaled-base
form. -/
theorem SampledInverseBoundedHamiltonianProducer.hamiltonian_eq_exp_growth
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    C.hamiltonian N =
      (((realDecayResidual lambda ((N : ℝ) * step))⁻¹ : ℝ) : ℂ) •
        C.baseHamiltonian := by
  rw [C.hamiltonian_scale N, C.scale_eq_exp_growth N]

/-- THEOREM 4: the produced bounded Hamiltonian remains self-adjoint at every
sampled step. -/
theorem SampledInverseBoundedHamiltonianProducer.hamiltonian_self_adjoint
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    IsSelfAdjoint (C.hamiltonian N) := by
  rw [C.hamiltonian_scale N]
  exact
    selfAdjointHamiltonian_real_smul
      C.baseHamiltonian (C.scale N) C.base_self_adjoint

/-- THEOREM 5: each produced bounded Hamiltonian supplies the Hamiltonian-side
self-adjoint generator certificate. -/
theorem SampledInverseBoundedHamiltonianProducer.generatorCertificate
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    SelfAdjointHamiltonianGeneratorCertificate E (C.hamiltonian N) :=
  selfAdjointHamiltonianGeneratorCertificate
    (C.hamiltonian N) (C.hamiltonian_self_adjoint N)

/-- THEOREM 6: each produced bounded Hamiltonian exponentiates to the bounded
self-adjoint unitary-flow certificate. -/
theorem SampledInverseBoundedHamiltonianProducer.exponentialGroupCertificate
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    BoundedSelfAdjointHamiltonianExponentialGroupCertificate E
      (C.hamiltonian N) :=
  boundedSelfAdjointHamiltonianExponentialGroupCertificate
    (C.hamiltonian N) (C.hamiltonian_self_adjoint N)

/-- THEOREM 7: each produced bounded Hamiltonian supplies the bounded
Schrödinger-flow certificate. -/
theorem SampledInverseBoundedHamiltonianProducer.schrodingerFlowCertificate
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate E
      (C.hamiltonian N) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    (C.hamiltonian N) (C.hamiltonian_self_adjoint N)

/-- THEOREM 8: the scalar coefficient of any faithful bounded-Hamiltonian
producer diverges under positive sampled scale. -/
theorem SampledInverseBoundedHamiltonianProducer.scale_tendsto_atTop
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hpos : 0 < lambda * step) :
    Tendsto C.scale atTop atTop :=
  (C.toScalarScaleProducer).scale_tendsto_atTop hpos

/-! ## Bundled receipt -/

/-- A compact receipt for the operator-level bridge: a carrier-produced scalar
coefficient applied to a supplied bounded self-adjoint base Hamiltonian yields
a sequence of bounded self-adjoint Hamiltonians with the expected exponential
unitary-flow and Schrödinger-flow certificates. -/
structure CarrierProducedBoundedHamiltonianReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (lambda step : ℝ)
    (C : SampledInverseBoundedHamiltonianProducer E lambda step) : Prop where
  scale_closed_form :
    ∀ N : ℕ,
      C.scale N = (realDecayResidual lambda ((N : ℝ) * step))⁻¹
  hamiltonian_closed_form :
    ∀ N : ℕ,
      C.hamiltonian N =
        (((realDecayResidual lambda ((N : ℝ) * step))⁻¹ : ℝ) : ℂ) •
          C.baseHamiltonian
  self_adjoint :
    ∀ N : ℕ, IsSelfAdjoint (C.hamiltonian N)
  generator :
    ∀ N : ℕ, SelfAdjointHamiltonianGeneratorCertificate E (C.hamiltonian N)
  exponential_group :
    ∀ N : ℕ,
      BoundedSelfAdjointHamiltonianExponentialGroupCertificate E
        (C.hamiltonian N)
  schrodinger_flow :
    ∀ N : ℕ,
      BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate E
        (C.hamiltonian N)
  coefficient_diverges :
    0 < lambda * step -> Tendsto C.scale atTop atTop

/-- THEOREM 9: every faithful sampled inverse bounded-Hamiltonian producer
supplies the operator-level receipt. -/
theorem carrierProducedBoundedHamiltonianReceipt
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step) :
    CarrierProducedBoundedHamiltonianReceipt E lambda step C where
  scale_closed_form := C.scale_eq_exp_growth
  hamiltonian_closed_form := C.hamiltonian_eq_exp_growth
  self_adjoint := C.hamiltonian_self_adjoint
  generator := C.generatorCertificate
  exponential_group := C.exponentialGroupCertificate
  schrodinger_flow := C.schrodingerFlowCertificate
  coefficient_diverges := fun hpos => C.scale_tendsto_atTop hpos

end AffineRelaxation
end SaturationMonoid
