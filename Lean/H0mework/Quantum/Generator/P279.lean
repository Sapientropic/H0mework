import H0mework.Quantum.Generator.P257

/-!
# Proposition 279: Stone-style unbounded Hamiltonian interface

P255-P257 prove the bounded-operator exponential direction:

* a bounded self-adjoint `H : E →L[ℂ] E` exponentiates to unitary time slices;
* those slices form a continuous one-parameter flow;
* the bounded exponential orbit satisfies the Schrödinger generator equation.

Physical Hamiltonians are often unbounded, so the bounded exponential theorem is
not the final physics interface.  This file does **not** prove Stone's theorem.
Instead it makes the Stone-side obligation explicit: a strongly continuous
unitary flow plus a dense invariant generator domain and an orbit-derivative
law for an unbounded Hamiltonian.

Once those Stone data are supplied, Lean proves the reusable bridge that was
previously only prose: the unbounded generator law gives the usual
Schrödinger normal form `i • dψ/dt = H ψ` on the certified domain, while the
flow carrier still supplies norm/distance/zero conservation.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Strongly continuous unitary flow carrier -/

/-- A Stone-side unitary flow carrier.

The homomorphism target `E ≃ₗᵢ[ℂ] E` already packages linearity, invertibility,
and isometry of each time slice.  The additional field is strong continuity:
every point orbit is continuous in real time. -/
structure StronglyContinuousUnitaryFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) : Prop where
  strong_continuous :
    ∀ x : E, Continuous (fun t : ℝ => U (Multiplicative.ofAdd t) x)

/-- A strongly continuous unitary flow still carries the conservation laws
forced by the `E ≃ₗᵢ[ℂ] E` carrier. -/
theorem StronglyContinuousUnitaryFlowCertificate.toIsometricConservation
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E)
    (_C : StronglyContinuousUnitaryFlowCertificate E U) :
    IsometricFlowConservationCertificate E U :=
  isometricFlowConservationCertificate U

/-! ## Dense unbounded Hamiltonian core -/

/-- A minimal domain-level carrier for an unbounded Hamiltonian.

This records the pieces that are meaningful before a full formal adjoint-domain
theory is available: a dense domain, a map defined only on that domain, and the
usual symmetry identity on the domain.  Full self-adjointness remains a later
producer obligation; this structure intentionally does not pretend that
symmetry alone is Stone's theorem. -/
structure DenseSymmetricUnboundedHamiltonianCore
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  domain : Set E
  H : {x : E // x ∈ domain} -> E
  dense_domain : Dense domain
  symmetric_on_domain :
    ∀ x y : {x : E // x ∈ domain},
      inner ℂ (H x) (y : E) = inner ℂ (x : E) (H y)

/-- A certified domain point evolved to time `t`. -/
def DenseSymmetricUnboundedHamiltonianCore.evolved
    (C : DenseSymmetricUnboundedHamiltonianCore E)
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E)
    (domain_invariant :
      ∀ t : ℝ, ∀ x : E, x ∈ C.domain ->
        U (Multiplicative.ofAdd t) x ∈ C.domain)
    (t : ℝ) (x : E) (hx : x ∈ C.domain) :
    {x : E // x ∈ C.domain} :=
  ⟨U (Multiplicative.ofAdd t) x, domain_invariant t x hx⟩

/-! ## Stone-style generator certificate -/

/-- The Stone-side certificate for an unbounded Hamiltonian generator.

The fields match the usable conclusion of Stone's theorem for this framework:
a strongly continuous unitary flow, a dense invariant generator domain, and
the orbit derivative `dψ/dt = -i • H ψ` on that domain. -/
structure StoneUnboundedHamiltonianGeneratorCertificate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E
  core : DenseSymmetricUnboundedHamiltonianCore E
  strong_flow : StronglyContinuousUnitaryFlowCertificate E U
  domain_invariant :
    ∀ t : ℝ, ∀ x : E, x ∈ core.domain ->
      U (Multiplicative.ofAdd t) x ∈ core.domain
  orbit_derivative :
    ∀ (t : ℝ) (x : E) (hx : x ∈ core.domain),
      HasDerivAt
        (fun τ : ℝ => U (Multiplicative.ofAdd τ) x)
        (-(Complex.I •
          core.H (core.evolved U domain_invariant t x hx))) t

namespace StoneUnboundedHamiltonianGeneratorCertificate

/-- The evolved domain point associated to a Stone certificate. -/
def evolved
    (C : StoneUnboundedHamiltonianGeneratorCertificate E)
    (t : ℝ) (x : E) (hx : x ∈ C.core.domain) :
    {x : E // x ∈ C.core.domain} :=
  C.core.evolved C.U C.domain_invariant t x hx

/-- THEOREM 1: the Stone certificate exposes strong continuity of each orbit. -/
theorem strongContinuous
    (C : StoneUnboundedHamiltonianGeneratorCertificate E) (x : E) :
    Continuous (fun t : ℝ => C.U (Multiplicative.ofAdd t) x) :=
  C.strong_flow.strong_continuous x

/-- THEOREM 2: the Stone certificate inherits norm/distance/zero conservation
from its unitary-flow carrier. -/
theorem toIsometricConservation
    (C : StoneUnboundedHamiltonianGeneratorCertificate E) :
    IsometricFlowConservationCertificate E C.U :=
  C.strong_flow.toIsometricConservation C.U

/-- THEOREM 3: the unbounded orbit derivative supplied by the Stone
certificate. -/
theorem orbitDerivative
    (C : StoneUnboundedHamiltonianGeneratorCertificate E)
    (t : ℝ) (x : E) (hx : x ∈ C.core.domain) :
    HasDerivAt
      (fun τ : ℝ => C.U (Multiplicative.ofAdd τ) x)
      (-(Complex.I • C.core.H (C.evolved t x hx))) t :=
  C.orbit_derivative t x hx

/-- The scalar algebra behind the Schrödinger normal form:
`i • (-(i • v)) = v`. -/
theorem complex_I_smul_neg_I_smul (v : E) :
    Complex.I • (-(Complex.I • v)) = v := by
  rw [smul_neg, smul_smul]
  norm_num

/-- THEOREM 4: on the certified dense invariant domain, the Stone generator
law has the usual Schrödinger normal form `i • dψ/dt = H ψ`. -/
theorem schrodingerNormalForm
    (C : StoneUnboundedHamiltonianGeneratorCertificate E)
    (t : ℝ) (x : E) (hx : x ∈ C.core.domain) :
    Complex.I •
        (-(Complex.I • C.core.H (C.evolved t x hx))) =
      C.core.H (C.evolved t x hx) :=
  complex_I_smul_neg_I_smul (C.core.H (C.evolved t x hx))

end StoneUnboundedHamiltonianGeneratorCertificate

/-! ## Bundled bridge certificate -/

/-- The exact bridge supplied by P279: Stone-side unbounded generator data
yield strong continuity, conservation, orbit derivative, and Schrödinger
normal form on the invariant domain. -/
structure StoneUnboundedHamiltonianSchrodingerBridge
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  stone : StoneUnboundedHamiltonianGeneratorCertificate E
  conservation : IsometricFlowConservationCertificate E stone.U
  strong_continuous :
    ∀ x : E, Continuous (fun t : ℝ => stone.U (Multiplicative.ofAdd t) x)
  orbit_derivative :
    ∀ (t : ℝ) (x : E) (hx : x ∈ stone.core.domain),
      HasDerivAt
        (fun τ : ℝ => stone.U (Multiplicative.ofAdd τ) x)
        (-(Complex.I • stone.core.H (stone.evolved t x hx))) t
  normal_form :
    ∀ (t : ℝ) (x : E) (hx : x ∈ stone.core.domain),
      Complex.I •
          (-(Complex.I • stone.core.H (stone.evolved t x hx))) =
        stone.core.H (stone.evolved t x hx)

/-- Build the P279 bridge from a Stone-side unbounded generator certificate. -/
def stoneUnboundedHamiltonianSchrodingerBridge
    (C : StoneUnboundedHamiltonianGeneratorCertificate E) :
    StoneUnboundedHamiltonianSchrodingerBridge E where
  stone := C
  conservation := C.toIsometricConservation
  strong_continuous := C.strongContinuous
  orbit_derivative := C.orbitDerivative
  normal_form := C.schrodingerNormalForm


end
end AffineRelaxation
end SaturationMonoid
