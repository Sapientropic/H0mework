import Mathlib.Analysis.InnerProductSpace.LinearPMap
import H0mework.Quantum.Generator.P279

/-!
# Proposition 283: LinearPMap bridge for Stone-side unbounded Hamiltonians

P279 intentionally stopped at a Stone-side certificate interface: a strongly
continuous unitary flow, a dense invariant domain, and an orbit-derivative law
for an unbounded Hamiltonian.  This file connects that interface to Mathlib's
current carrier for unbounded operators, `LinearPMap`.

Boundary: this is **not** Stone's theorem.  It does not construct a
self-adjoint generator from an arbitrary strongly continuous unitary group.
It proves the adapter we need once such a generator is supplied as a
Mathlib `LinearPMap`.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Mathlib LinearPMap Hamiltonian core -/

/-- A Mathlib-backed unbounded Hamiltonian core.

The operator is a partially defined linear map.  Its domain is dense, and it is
symmetric in Mathlib's formal-adjoint sense.  Full self-adjointness is stronger
and remains the real Stone-theorem producer obligation. -/
structure LinearPMapHamiltonianCore (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  operator : E →ₗ.[ℂ] E
  dense_domain : Dense (operator.domain : Set E)
  symmetric : operator.IsFormalAdjoint operator

namespace LinearPMapHamiltonianCore

/-- The set-level domain used by P279. -/
def domainSet (C : LinearPMapHamiltonianCore E) : Set E :=
  (C.operator.domain : Set E)

/-- Evaluate the partial Hamiltonian on its certified domain. -/
def applyOnDomain (C : LinearPMapHamiltonianCore E) :
    {x : E // x ∈ C.domainSet} -> E :=
  fun x => C.operator ⟨x.1, x.2⟩

/-- THEOREM 1: a `LinearPMapHamiltonianCore` is a P279 dense symmetric
unbounded Hamiltonian core. -/
def toDenseSymmetricUnboundedHamiltonianCore
    (C : LinearPMapHamiltonianCore E) :
    DenseSymmetricUnboundedHamiltonianCore E where
  domain := C.domainSet
  H := C.applyOnDomain
  dense_domain := C.dense_domain
  symmetric_on_domain := by
    intro x y
    exact C.symmetric ⟨x.1, x.2⟩ ⟨y.1, y.2⟩

/-- THEOREM 2: self-adjoint `LinearPMap`s are symmetric in the formal-adjoint
sense required by the core. -/
theorem isSelfAdjoint_isFormalAdjoint
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have hDense : Dense (A.domain : Set E) := hA.dense_domain
  have hAdj : (LinearPMap.adjoint A).IsFormalAdjoint A :=
    LinearPMap.adjoint_isFormalAdjoint hDense
  have hEq : LinearPMap.adjoint A = A :=
    (LinearPMap.isSelfAdjoint_def).mp hA
  simpa [hEq] using hAdj

/-- THEOREM 3: a self-adjoint `LinearPMap` automatically supplies the dense
symmetric core fields. -/
def ofSelfAdjoint
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    LinearPMapHamiltonianCore E where
  operator := A
  dense_domain := hA.dense_domain
  symmetric := isSelfAdjoint_isFormalAdjoint hA

end LinearPMapHamiltonianCore

/-! ## Stone-side generator certificate using LinearPMap -/

/-- A Stone-side generator certificate whose Hamiltonian is a Mathlib
`LinearPMap`.

Supplying this is still the Stone theorem / physics producer obligation.  Once
it is supplied, the P279 bridge is available without changing downstream code. -/
structure StoneLinearPMapGeneratorCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E
  core : LinearPMapHamiltonianCore E
  strong_flow : StronglyContinuousUnitaryFlowCertificate E U
  domain_invariant :
    ∀ t : ℝ, ∀ x : E, x ∈ core.domainSet ->
      U (Multiplicative.ofAdd t) x ∈ core.domainSet
  orbit_derivative :
    ∀ (t : ℝ) (x : E) (hx : x ∈ core.domainSet),
      HasDerivAt
        (fun τ : ℝ => U (Multiplicative.ofAdd τ) x)
        (-(Complex.I •
          core.operator ⟨U (Multiplicative.ofAdd t) x,
            domain_invariant t x hx⟩)) t

namespace StoneLinearPMapGeneratorCertificate

/-- THEOREM 4: forget the `LinearPMap` carrier to the P279 Stone-side
certificate. -/
def toStoneUnboundedHamiltonianGeneratorCertificate
    (C : StoneLinearPMapGeneratorCertificate E) :
    StoneUnboundedHamiltonianGeneratorCertificate E where
  U := C.U
  core := C.core.toDenseSymmetricUnboundedHamiltonianCore
  strong_flow := C.strong_flow
  domain_invariant := C.domain_invariant
  orbit_derivative := by
    intro t x hx
    exact C.orbit_derivative t x hx

/-- THEOREM 5: a Mathlib-backed Stone certificate inherits the P279
Schrödinger bridge. -/
def toSchrodingerBridge
    (C : StoneLinearPMapGeneratorCertificate E) :
    StoneUnboundedHamiltonianSchrodingerBridge E :=
  stoneUnboundedHamiltonianSchrodingerBridge
    C.toStoneUnboundedHamiltonianGeneratorCertificate

omit [CompleteSpace E] in
/-- THEOREM 6: the bridge exposes conservation laws through the P279 carrier. -/
theorem conservation
    (C : StoneLinearPMapGeneratorCertificate E) :
    IsometricFlowConservationCertificate E C.U :=
  C.toStoneUnboundedHamiltonianGeneratorCertificate.toIsometricConservation

omit [CompleteSpace E] in
/-- THEOREM 7: the LinearPMap-backed certificate gives the Schrödinger normal
form on its invariant domain. -/
theorem schrodingerNormalForm
    (C : StoneLinearPMapGeneratorCertificate E)
    (t : ℝ) (x : E) (hx : x ∈ C.core.domainSet) :
    Complex.I •
        (-(Complex.I •
          C.core.operator ⟨C.U (Multiplicative.ofAdd t) x,
            C.domain_invariant t x hx⟩)) =
      C.core.operator ⟨C.U (Multiplicative.ofAdd t) x,
        C.domain_invariant t x hx⟩ :=
  C.toStoneUnboundedHamiltonianGeneratorCertificate.schrodingerNormalForm t x hx

end StoneLinearPMapGeneratorCertificate


end
end AffineRelaxation
end SaturationMonoid
