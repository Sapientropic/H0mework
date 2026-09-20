import H0mework.Quantum.Generator.P255
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Proposition 256: bounded Hamiltonian exponential slices form a one-parameter flow

P255 proves that a bounded self-adjoint Hamiltonian exponentiates to unitary
time slices.  This file adds the bounded exponential flow laws:

* the zero time slice is `1`;
* time addition is sent to multiplication of slices;
* the slice map is continuous.

Together with P255's unitary-slice theorem, this gives a bounded
self-adjoint-Hamiltonian one-parameter unitary-flow certificate.

Boundary: this is still the bounded-operator exponential direction.  It is not
Stone's theorem, does not derive a self-adjoint generator from an arbitrary
strongly continuous unitary flow, and does not handle unbounded Hamiltonians.
-/

noncomputable section

open NormedSpace

namespace SaturationMonoid
namespace AffineRelaxation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded Hamiltonian exponential slice at time zero is the identity
operator. -/
theorem boundedHamiltonian_exponentialSlice_zero
    (H : E →L[ℂ] E) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • (-Complex.I • H)) = (1 : E →L[ℂ] E) := by
  simp

/-- Bounded Hamiltonian exponential slices compose by addition of real time. -/
theorem boundedHamiltonian_exponentialSlice_add
    (H : E →L[ℂ] E) (t s : ℝ) :
    NormedSpace.exp (((t + s : ℝ) : ℂ) • (-Complex.I • H)) =
      NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) *
        NormedSpace.exp ((s : ℂ) • (-Complex.I • H)) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) :=
    NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hsum : (((t + s : ℝ) : ℂ) • (-Complex.I • H)) =
      (t : ℂ) • (-Complex.I • H) + (s : ℂ) • (-Complex.I • H) := by
    simp [add_smul, add_comm]
  rw [hsum]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl (-Complex.I • H)).smul_left (t : ℂ)).smul_right (s : ℂ))

/-- The bounded Hamiltonian exponential slice map is continuous in real time. -/
theorem continuous_boundedHamiltonian_exponentialSlice
    (H : E →L[ℂ] E) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-Complex.I • H))) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) :=
    NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  apply NormedSpace.exp_continuous.comp
  fun_prop

/-- A bounded self-adjoint Hamiltonian supplies a continuous one-parameter
unitary exponential flow. -/
structure BoundedSelfAdjointHamiltonianExponentialGroupCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) : Prop where
  exponential_unitary :
    BoundedSelfAdjointHamiltonianExponentialFlowCertificate E H
  zero_slice :
    NormedSpace.exp (((0 : ℝ) : ℂ) • (-Complex.I • H)) = (1 : E →L[ℂ] E)
  add_slice :
    ∀ t s : ℝ,
      NormedSpace.exp (((t + s : ℝ) : ℂ) • (-Complex.I • H)) =
        NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) *
          NormedSpace.exp ((s : ℂ) • (-Complex.I • H))
  continuous_slice :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-Complex.I • H)))

/-- Build the bounded self-adjoint Hamiltonian exponential group certificate
from self-adjointness. -/
theorem boundedSelfAdjointHamiltonianExponentialGroupCertificate
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    BoundedSelfAdjointHamiltonianExponentialGroupCertificate E H where
  exponential_unitary := boundedSelfAdjointHamiltonianExponentialFlowCertificate H hH
  zero_slice := boundedHamiltonian_exponentialSlice_zero H
  add_slice := boundedHamiltonian_exponentialSlice_add H
  continuous_slice := continuous_boundedHamiltonian_exponentialSlice H

/-- Forget the group certificate back to the P255 unitary-slice certificate. -/
theorem BoundedSelfAdjointHamiltonianExponentialGroupCertificate.toExponentialFlow
    {H : E →L[ℂ] E}
    (C : BoundedSelfAdjointHamiltonianExponentialGroupCertificate E H) :
    BoundedSelfAdjointHamiltonianExponentialFlowCertificate E H :=
  C.exponential_unitary

/-- The P256 certificate exposes the unitary time-slice law from P255. -/
theorem BoundedSelfAdjointHamiltonianExponentialGroupCertificate.unitarySlice
    {H : E →L[ℂ] E}
    (C : BoundedSelfAdjointHamiltonianExponentialGroupCertificate E H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) ∈ unitary (E →L[ℂ] E) :=
  C.exponential_unitary.unitarySlice t

/-- The P256 certificate exposes time-additive multiplication of exponential
slices. -/
theorem BoundedSelfAdjointHamiltonianExponentialGroupCertificate.addSlice
    {H : E →L[ℂ] E}
    (C : BoundedSelfAdjointHamiltonianExponentialGroupCertificate E H) (t s : ℝ) :
    NormedSpace.exp (((t + s : ℝ) : ℂ) • (-Complex.I • H)) =
      NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) *
        NormedSpace.exp ((s : ℂ) • (-Complex.I • H)) :=
  C.add_slice t s


end AffineRelaxation
end SaturationMonoid
