import H0mework.Realization.CyclicMemory.P117
import H0mework.Physics.Lie.P286
import H0mework.Arithmetic.PrimeShadow.P342

/-!
# Proposition 343: SM-allowed prime-edge cycles as the Goldbach obstruction gate

The proposed Standard-Model route should not be phrased as "confinement proves
Goldbach" without an admissibility theorem.  What the gauge/facet layer must
supply is an allowed-sector classifier for prime-edge three-cycles:

* a prime-edge triangle encodes a proposed equation `p + q = 2n`;
* edge exactness of that triangle is exactly that equation;
* non-exactness is a genuine three-agent H¹ obstruction;
* an SM-allowed obstruction is equivalent to Goldbach failure only after the
  allowed sector is proved sound and complete for those obstructions.

This file proves that exact bridge and leaves the physics obligation in the
right place: the concrete `SU(3)×SU(2)×U(1) ⊂ SU(7)` embedding is available
from P286, but the Standard-Model representation/action must still prove the
allowed-sector soundness/completeness certificate.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open GaugeProjection

/-! ## Prime-edge three-cycle encoding of a Goldbach equation -/

/-- The three-agent prime-edge cochain for the equation `p + q = 2n`.
The selected ring edges are

`t0 -> t1 = p`, `t1 -> t2 = q`, and `t2 -> t0 = -2n`.

Thus the accumulated ring residual is `p + q - 2n`. -/
def primeEdgeThreeCycleCochain
    (n : ℕ) (p q : PrimeExponent) :
    ThreeCycleTime -> ThreeCycleTime -> Int
  | ThreeCycleTime.t0, ThreeCycleTime.t1 => (p.1 : Int)
  | ThreeCycleTime.t1, ThreeCycleTime.t2 => (q.1 : Int)
  | ThreeCycleTime.t2, ThreeCycleTime.t0 => -((2 * n : ℕ) : Int)
  | _, _ => 0

/-- THEOREM 1: the three-agent residual is exactly the arithmetic defect
`p + q - 2n`. -/
theorem primeEdgeThreeCycle_residual_eq
    (n : ℕ) (p q : PrimeExponent) :
    threeAgentRingResidual (primeEdgeThreeCycleCochain n p q) =
      (p.1 : Int) + (q.1 : Int) - ((2 * n : ℕ) : Int) := by
  simp [threeAgentRingResidual, primeEdgeThreeCycleCochain]
  ring

/-- THEOREM 2: selected-edge exactness of the prime-edge three-cycle is exactly
the ordinary Goldbach equation for that pair. -/
theorem primeEdgeThreeCycle_edgeExact_iff
    (n : ℕ) (p q : PrimeExponent) :
    ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q) ↔
      2 * n = p.1 + q.1 := by
  constructor
  · intro hexact
    have hzero :
        threeAgentRingResidual (primeEdgeThreeCycleCochain n p q) = 0 :=
      (threeAgentRingEdgeExact_iff_residual_zero
        (primeEdgeThreeCycleCochain n p q)).mp hexact
    rw [primeEdgeThreeCycle_residual_eq] at hzero
    omega
  · intro hsum
    apply (threeAgentRingEdgeExact_iff_residual_zero
      (primeEdgeThreeCycleCochain n p q)).mpr
    rw [primeEdgeThreeCycle_residual_eq]
    omega

/-- A prime-edge three-cycle is obstructed when the selected ring is not exact. -/
def PrimeEdgeThreeCycleObstructed
    (n : ℕ) (p q : PrimeExponent) : Prop :=
  Not (ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q))

/-- THEOREM 3: obstruction is exactly failure of the pair equation. -/
theorem primeEdgeThreeCycle_obstructed_iff
    (n : ℕ) (p q : PrimeExponent) :
    PrimeEdgeThreeCycleObstructed n p q ↔
      2 * n ≠ p.1 + q.1 := by
  rw [PrimeEdgeThreeCycleObstructed, primeEdgeThreeCycle_edgeExact_iff]

/-- THEOREM 4: an obstructed prime-edge three-cycle gives a genuine H¹
obstruction on the three-agent skeleton. -/
theorem primeEdgeThreeCycle_obstructed_h1
    {n : ℕ} {p q : PrimeExponent}
    (hobs : PrimeEdgeThreeCycleObstructed n p q) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      (primeEdgeThreeCycleCochain n p q) := by
  have hres :
      threeAgentRingResidual (primeEdgeThreeCycleCochain n p q) ≠ 0 := by
    intro hzero
    exact hobs
      ((threeAgentRingEdgeExact_iff_residual_zero
        (primeEdgeThreeCycleCochain n p q)).mpr hzero)
  exact threeAgentRingResidual_nonzero_h1
    (primeEdgeThreeCycleCochain n p q) hres

/-! ## SM-allowed sector boundary -/

/-- A concrete Standard-Model / seven-facet sector together with a predicate
selecting the prime-edge three-cycle configurations allowed by that sector.

The embedding field is the already-proved compact block embedding target from
P270/P286.  The hard future work is to derive `allowed` from the actual
Standard-Model representation action instead of supplying it abstractly. -/
structure SMAllowedPrimeEdgeSector where
  smEmbedding : SU7StandardModelBreakingChainCertificate
  allowed : ℕ -> PrimeExponent -> PrimeExponent -> Prop

/-- The current concrete SU(7) block embedding can host any proposed allowed
predicate.  This is only the carrier/embedding, not the representation-action
producer. -/
noncomputable def concreteSMAllowedPrimeEdgeSector
    (allowed : ℕ -> PrimeExponent -> PrimeExponent -> Prop) :
    SMAllowedPrimeEdgeSector where
  smEmbedding := ConcreteBlockDiagonal.concreteSU7BreakingChainCertificate
  allowed := allowed

/-- There exists an SM-allowed obstructed prime-edge three-cycle. -/
def SMAllowedObstructedPrimeEdgeCycle
    (S : SMAllowedPrimeEdgeSector) : Prop :=
  ∃ n : ℕ, ∃ p q : PrimeExponent,
    2 ≤ n ∧ S.allowed n p q ∧ PrimeEdgeThreeCycleObstructed n p q

/-- The exact admissibility obligation the Standard-Model/facet layer must
prove if it is to make the proposed "SM excludes Goldbach obstruction" route
mathematically real.

`obstruction_sound`: an allowed obstruction is not just a bad pair; it is a
real witness that the corresponding even number has no two-prime decomposition.

`obstruction_complete`: if an even number has no two-prime decomposition, the
allowed sector exposes that failure as an allowed obstructed prime-edge cycle.
-/
structure SMGoldbachObstructionClassifier
    (S : SMAllowedPrimeEdgeSector) : Prop where
  obstruction_sound :
    ∀ {n : ℕ} {p q : PrimeExponent},
      2 ≤ n -> S.allowed n p q ->
        PrimeEdgeThreeCycleObstructed n p q ->
          ¬ HasPrimeAdditiveDecomposition (2 * n)
  obstruction_complete :
    ∀ {n : ℕ}, 2 ≤ n ->
      ¬ HasPrimeAdditiveDecomposition (2 * n) ->
        ∃ p q : PrimeExponent,
          S.allowed n p q ∧ PrimeEdgeThreeCycleObstructed n p q

/-- THEOREM 5: under an SM/facet obstruction classifier, an allowed obstructed
prime-edge cycle is exactly ordinary Goldbach failure. -/
theorem smAllowedObstructedPrimeEdgeCycle_iff_not_evenGoldbach
    {S : SMAllowedPrimeEdgeSector}
    (C : SMGoldbachObstructionClassifier S) :
    SMAllowedObstructedPrimeEdgeCycle S ↔ ¬ EvenGoldbachStatement := by
  constructor
  · rintro ⟨n, p, q, hn, hallowed, hobs⟩ hgoldbach
    exact (C.obstruction_sound hn hallowed hobs) (hgoldbach n hn)
  · intro hnot
    classical
    by_contra hno
    apply hnot
    intro n hn
    by_contra hbad
    rcases C.obstruction_complete hn hbad with ⟨p, q, hallowed, hobs⟩
    exact hno ⟨n, p, q, hn, hallowed, hobs⟩

/-- THEOREM 6: equivalently, absence of SM-allowed prime-edge obstructions is
exactly ordinary Goldbach, provided the SM/facet classifier has been proved. -/
theorem no_smAllowedObstructedPrimeEdgeCycle_iff_evenGoldbach
    {S : SMAllowedPrimeEdgeSector}
    (C : SMGoldbachObstructionClassifier S) :
    ¬ SMAllowedObstructedPrimeEdgeCycle S ↔ EvenGoldbachStatement := by
  classical
  rw [smAllowedObstructedPrimeEdgeCycle_iff_not_evenGoldbach C]
  constructor
  · exact not_not.mp
  · exact not_not.mpr

/-- THEOREM 7: if an SM-allowed obstructed prime-edge cycle is exhibited, the
associated phase cochain carries a concrete H¹ obstruction. -/
theorem smAllowedObstructedPrimeEdgeCycle_h1
    {S : SMAllowedPrimeEdgeSector}
    (h : SMAllowedObstructedPrimeEdgeCycle S) :
    ∃ n : ℕ, ∃ p q : PrimeExponent,
      2 ≤ n ∧ S.allowed n p q ∧
        CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover ThreeCycleTime Int)
          (primeEdgeThreeCycleCochain n p q) := by
  rcases h with ⟨n, p, q, hn, hallowed, hobs⟩
  exact ⟨n, p, q, hn, hallowed, primeEdgeThreeCycle_obstructed_h1 hobs⟩

/-- A compact certificate for the SM-allowed Goldbach obstruction gate. -/
structure P343SMAllowedGoldbachGateCertificate
    (S : SMAllowedPrimeEdgeSector) : Prop where
  prime_edge_exact_iff :
    ∀ n p q,
      ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q) ↔
        2 * n = p.1 + q.1
  prime_edge_obstructed_iff :
    ∀ n p q, PrimeEdgeThreeCycleObstructed n p q ↔
      2 * n ≠ p.1 + q.1
  prime_edge_obstructed_h1 :
    ∀ {n p q}, PrimeEdgeThreeCycleObstructed n p q ->
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (primeEdgeThreeCycleCochain n p q)
  allowed_obstruction_iff_not_goldbach :
    SMGoldbachObstructionClassifier S ->
      (SMAllowedObstructedPrimeEdgeCycle S ↔ ¬ EvenGoldbachStatement)
  no_allowed_obstruction_iff_goldbach :
    SMGoldbachObstructionClassifier S ->
      (¬ SMAllowedObstructedPrimeEdgeCycle S ↔ EvenGoldbachStatement)
  allowed_obstruction_h1 :
    SMAllowedObstructedPrimeEdgeCycle S ->
      ∃ n : ℕ, ∃ p q : PrimeExponent,
        2 ≤ n ∧ S.allowed n p q ∧
          CechAdditiveCover.H1Obstruction
            (identityPairZeroTripleCover ThreeCycleTime Int)
            (primeEdgeThreeCycleCochain n p q)

/-- THEOREM 8: every SM-allowed sector carries the formal obstruction-gate
certificate; the missing datum is exactly the `SMGoldbachObstructionClassifier`
argument demanded by the iff fields. -/
theorem p343SMAllowedGoldbachGateCertificate
    (S : SMAllowedPrimeEdgeSector) :
    P343SMAllowedGoldbachGateCertificate S where
  prime_edge_exact_iff := primeEdgeThreeCycle_edgeExact_iff
  prime_edge_obstructed_iff := primeEdgeThreeCycle_obstructed_iff
  prime_edge_obstructed_h1 := by
    intro n p q hobs
    exact primeEdgeThreeCycle_obstructed_h1 hobs
  allowed_obstruction_iff_not_goldbach := by
    intro C
    exact smAllowedObstructedPrimeEdgeCycle_iff_not_evenGoldbach C
  no_allowed_obstruction_iff_goldbach := by
    intro C
    exact no_smAllowedObstructedPrimeEdgeCycle_iff_evenGoldbach C
  allowed_obstruction_h1 := smAllowedObstructedPrimeEdgeCycle_h1

end AffineRelaxation
end SaturationMonoid
