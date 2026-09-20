import H0mework.Quantum.Generator.P254
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Proposition 255: bounded self-adjoint Hamiltonians exponentiate to unitary slices

P254 proves the polarity layer: a self-adjoint bounded Hamiltonian `H` gives a
skew-adjoint generator `-i • H`.  This file pushes one step further on the
bounded-operator side: every real time slice of the exponential flow

`exp ((t : ℂ) • (-i • H))`

is unitary.

Boundary: this is still a bounded Banach/C*-algebra exponential statement.  It
does not prove Stone's theorem, does not construct a self-adjoint generator
from an arbitrary strongly continuous unitary flow, and does not cover
unbounded physical Hamiltonians.
-/

noncomputable section

open NormedSpace

namespace SaturationMonoid
namespace AffineRelaxation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Real time rescaling preserves the skew-adjoint generator obtained from a
self-adjoint bounded Hamiltonian. -/
theorem selfAdjointHamiltonian_realTime_skewGenerator
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    ((t : ℂ) • (-Complex.I • H)) ∈ skewAdjoint (E →L[ℂ] E) := by
  have hg : (-Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E) :=
    selfAdjointHamiltonian_skewGenerator H hH
  rw [skewAdjoint.mem_iff] at hg ⊢
  rw [star_smul, hg]
  have ht : star (t : ℂ) = (t : ℂ) := by
    simp
  rw [ht]
  simp

/-- A bounded self-adjoint Hamiltonian has unitary exponential time slices. -/
theorem selfAdjointHamiltonian_exponentialSlice_unitary
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) ∈ unitary (E →L[ℂ] E) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) :=
    NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (selfAdjointHamiltonian_realTime_skewGenerator H hH t)

/-- Certificate packaging for the bounded exponential-flow bridge. -/
structure BoundedSelfAdjointHamiltonianExponentialFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) where
  self_adjoint : IsSelfAdjoint H
  skew_generator :
    (-Complex.I • H) ∈ skewAdjoint (E →L[ℂ] E)
  real_time_skew_generator :
    ∀ t : ℝ, ((t : ℂ) • (-Complex.I • H)) ∈ skewAdjoint (E →L[ℂ] E)
  unitary_exponential_slice :
    ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) ∈ unitary (E →L[ℂ] E)

/-- Build the bounded exponential-flow certificate from self-adjointness. -/
theorem boundedSelfAdjointHamiltonianExponentialFlowCertificate
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    BoundedSelfAdjointHamiltonianExponentialFlowCertificate E H where
  self_adjoint := hH
  skew_generator := selfAdjointHamiltonian_skewGenerator H hH
  real_time_skew_generator := selfAdjointHamiltonian_realTime_skewGenerator H hH
  unitary_exponential_slice := selfAdjointHamiltonian_exponentialSlice_unitary H hH

/-- Forget the P255 certificate back to the P254 polarity certificate. -/
theorem BoundedSelfAdjointHamiltonianExponentialFlowCertificate.toGeneratorCertificate
    {H : E →L[ℂ] E}
    (C : BoundedSelfAdjointHamiltonianExponentialFlowCertificate E H) :
    SelfAdjointHamiltonianGeneratorCertificate E H where
  self_adjoint := C.self_adjoint
  skew_generator := C.skew_generator

/-- The P255 certificate exposes the unitary exponential slice at every real
time. -/
theorem BoundedSelfAdjointHamiltonianExponentialFlowCertificate.unitarySlice
    {H : E →L[ℂ] E}
    (C : BoundedSelfAdjointHamiltonianExponentialFlowCertificate E H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (-Complex.I • H)) ∈ unitary (E →L[ℂ] E) :=
  C.unitary_exponential_slice t

/-- Real scalar identity Hamiltonians are a concrete bounded family covered by
the P255 bridge. -/
theorem realScalarIdentityHamiltonian_exponentialSlice_unitary
    (omega t : ℝ) :
    NormedSpace.exp
        ((t : ℂ) • (-Complex.I • ((omega : ℂ) • (1 : E →L[ℂ] E)))) ∈
      unitary (E →L[ℂ] E) := by
  have hOne : IsSelfAdjoint (1 : E →L[ℂ] E) := by
    simp [IsSelfAdjoint]
  have hH : IsSelfAdjoint ((omega : ℂ) • (1 : E →L[ℂ] E)) :=
    selfAdjointHamiltonian_real_smul (1 : E →L[ℂ] E) omega hOne
  exact selfAdjointHamiltonian_exponentialSlice_unitary
    ((omega : ℂ) • (1 : E →L[ℂ] E)) hH t


end AffineRelaxation
end SaturationMonoid
