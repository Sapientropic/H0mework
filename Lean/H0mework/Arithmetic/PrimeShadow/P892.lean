import H0mework.Physics.RunningSources.P891

/-!
# Proposition 892: non-storing physical branch cells project to prime edges

P884 put the transition producer below prime-edge storage: a
`SU7PhysicalBranchingSpectrumCell` carries physical SU(7) atoms, a branch label,
and a gauge-allowed color loop.  It stores no `PrimeExponent`, no `Nat.Prime`
field, and no Goldbach pair.

This file isolates the projection boundary requested by the proof spine.  The
projection from a physical branch-spectrum cell to a prime-edge branch cell is
computed, not read from stored prime data:

* first forget the gauge wrapper to the P881 prime-coded spectrum cell;
* then apply the P879 canonical atom readout;
* the resulting left/right edge labels are prime because the readout theorem
  proves it;
* zero physical-spectrum residual then computes a trace-zero prime-edge loop.

Thus the cell remains representation/gauge data only, while the prime-edge
object appears only as the faithful projection output.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Direct prime-edge projection from non-storing physical cells -/

/-- Prime-edge projection of a physical SU(7) branch-spectrum cell.

The input cell stores no prime edge.  The output prime proofs are produced by
the canonical physical atom readout from P879/P884. -/
def primeEdgeBranchCell_of_physicalBranchingSpectrumCell
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    SU7PrimeEdgeBranchCell n :=
  primeEdgeBranchCell_of_primeCodedSpectrumCell
    (primeCodedSpectrumCell_of_physicalSpectrumCell C)

/-- THEOREM 1: the left projected edge is exactly the generated physical atom
code. -/
@[simp] theorem primeEdgeBranchCell_of_physicalBranchingSpectrumCell_left
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).leftPrime.1 =
      su7PhysicalAtomCode C.leftAtom := rfl

/-- THEOREM 2: the right projected edge is exactly the generated physical atom
code. -/
@[simp] theorem primeEdgeBranchCell_of_physicalBranchingSpectrumCell_right
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).rightPrime.1 =
      su7PhysicalAtomCode C.rightAtom := rfl

/-- THEOREM 3: the left projected edge is prime. -/
theorem physicalBranchingSpectrumCell_leftPrime_generated
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    Nat.Prime
      (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).leftPrime.1 :=
  (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).leftPrime.2

/-- THEOREM 4: the right projected edge is prime. -/
theorem physicalBranchingSpectrumCell_rightPrime_generated
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    Nat.Prime
      (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).rightPrime.1 :=
  (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).rightPrime.2

/-- THEOREM 5: prime-edge projection preserves the physical branch-spectrum
residual. -/
theorem branchWeightResidual_physicalProjection_eq
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    branchWeightResidual
        (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C) =
      physicalBranchingSpectrumResidual C := by
  rfl

/-- THEOREM 6: zero physical residual makes the projected prime-edge cell
trace-neutral. -/
theorem traceNeutral_of_physicalBranchingSpectrumResidual_zero
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : physicalBranchingSpectrumResidual C = 0) :
    (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).traceNeutral := by
  exact
    (branchWeightResidual_eq_zero_iff_traceNeutral
      (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C)).mp
      (by simpa [branchWeightResidual_physicalProjection_eq C] using hzero)

/-- THEOREM 7: zero physical residual computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_physicalBranchingSpectrumResidual
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : physicalBranchingSpectrumResidual C = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C)
    (traceNeutral_of_physicalBranchingSpectrumResidual_zero C hzero)

/-- THEOREM 8: a physical transition system produces a projected trace-zero
prime-edge loop without storing one in the transition data. -/
def traceZeroPrimeEdgeLoop_of_physicalTransitionSystem
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) :
    TraceZeroPrimeEdgeLoop n :=
  let Z := Classical.choose (exists_zeroCell_of_physicalTransitionSystem T)
  let hZ := Classical.choose_spec
    (exists_zeroCell_of_physicalTransitionSystem T)
  traceZeroPrimeEdgeLoop_of_physicalBranchingSpectrumResidual Z hZ.2.2

/-- THEOREM 9: the projected transition loop has the generated left prime
edge. -/
theorem traceZeroPrimeEdgeLoop_of_physicalTransitionSystem_leftPrime
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) :
    Nat.Prime
      (traceZeroPrimeEdgeLoop_of_physicalTransitionSystem T).leftPrime.1 :=
  (traceZeroPrimeEdgeLoop_of_physicalTransitionSystem T).leftPrime.2

/-- THEOREM 10: the projected transition loop has the generated right prime
edge. -/
theorem traceZeroPrimeEdgeLoop_of_physicalTransitionSystem_rightPrime
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) :
    Nat.Prime
      (traceZeroPrimeEdgeLoop_of_physicalTransitionSystem T).rightPrime.1 :=
  (traceZeroPrimeEdgeLoop_of_physicalTransitionSystem T).rightPrime.2

/-! ## Certificate -/

/-- P892 certificate: the branch-spectrum producer cell remains below
prime-edge data; the prime-edge loop is generated only by projection after a
zero physical residual is produced. -/
structure SU7NonStoringPhysicalBranchingProjectionCertificate where
  project_cell :
    ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumCell n ->
      SU7PrimeEdgeBranchCell n
  projected_left_prime :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      Nat.Prime
        (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).leftPrime.1
  projected_right_prime :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      Nat.Prime
        (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).rightPrime.1
  projection_preserves_residual :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      branchWeightResidual
          (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C) =
        physicalBranchingSpectrumResidual C
  residual_zero_to_trace_neutral :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      physicalBranchingSpectrumResidual C = 0 ->
        (primeEdgeBranchCell_of_physicalBranchingSpectrumCell C).traceNeutral
  residual_zero_to_trace_zero_loop :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      physicalBranchingSpectrumResidual C = 0 ->
        TraceZeroPrimeEdgeLoop n
  transition_to_trace_zero_loop :
    ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumTransitionSystem n ->
      TraceZeroPrimeEdgeLoop n

def su7NonStoringPhysicalBranchingProjectionCertificate :
    SU7NonStoringPhysicalBranchingProjectionCertificate where
  project_cell := primeEdgeBranchCell_of_physicalBranchingSpectrumCell
  projected_left_prime :=
    physicalBranchingSpectrumCell_leftPrime_generated
  projected_right_prime :=
    physicalBranchingSpectrumCell_rightPrime_generated
  projection_preserves_residual :=
    branchWeightResidual_physicalProjection_eq
  residual_zero_to_trace_neutral :=
    traceNeutral_of_physicalBranchingSpectrumResidual_zero
  residual_zero_to_trace_zero_loop :=
    traceZeroPrimeEdgeLoop_of_physicalBranchingSpectrumResidual
  transition_to_trace_zero_loop :=
    traceZeroPrimeEdgeLoop_of_physicalTransitionSystem


end
end StandardModelConstraint
end SaturationMonoid
