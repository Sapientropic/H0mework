import H0mework.Physics.BranchSources.P1026

/-!
# Proposition 1028: additive-code data generates explicit branch/tensor hits

P1026 introduced the explicit `SU7BranchTensorGenerator`, but its completeness
theorem was still a bare hit hypothesis:

```lean
forall n hn, exists cand in G.candidates n hn, cand.residual = (0,0)
```

This file removes that bare hypothesis for the P1019 terminal residual-split
surface.  Given `DirectedCycleAdditiveCodeData`, Lean now constructs a concrete
singleton branch/tensor generator and proves that it hits zero residual on
every active fiber.

This is still not the final SU(7)/P710 producer.  The remaining hard producer
is precisely to build the additive-code data from the physical
representation/confinement carrier.  But the P1026 generator-hit receipt is no
longer a free-standing assumption.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Choosing the terminal two-primitive split -/

/-- A packaged two-primitive split at one active fiber. -/
def AdditiveCodeSplit
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) : Type :=
  { p : DirectedCycle × DirectedCycle //
      PrimitiveCycle p.1 ∧ PrimitiveCycle p.2 ∧
        S.glue p.1 p.2 = D.cycleOfFiber n hn }

/-- The P1017 terminal split for the fiber cycle supplied by additive-code
data, packaged as a pair. -/
def additiveCodeFiberSplit
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    AdditiveCodeSplit D n hn :=
  Classical.choice (by
    rcases
      evenCycle_twoPrimitiveDecomposition S (D.cycleOfFiber n hn)
        (D.cycle_even n hn)
        (D.cycle_closed n hn)
        (D.cycle_terminal n hn) with
      ⟨A, B, hA, hB, hglue⟩
    exact ⟨⟨(A, B), hA, hB, hglue⟩⟩)

/-- Left primitive cycle selected from the terminal split. -/
def additiveCodeLeftCycle
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) : DirectedCycle :=
  (additiveCodeFiberSplit D n hn).1.1

/-- Right primitive cycle selected from the terminal split. -/
def additiveCodeRightCycle
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) : DirectedCycle :=
  (additiveCodeFiberSplit D n hn).1.2

theorem additiveCodeLeftCycle_primitive
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    PrimitiveCycle (additiveCodeLeftCycle D n hn) := by
  exact (additiveCodeFiberSplit D n hn).2.1

theorem additiveCodeRightCycle_primitive
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    PrimitiveCycle (additiveCodeRightCycle D n hn) := by
  exact (additiveCodeFiberSplit D n hn).2.2.1

theorem additiveCodeGlue_eq_cycle
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    S.glue (additiveCodeLeftCycle D n hn)
        (additiveCodeRightCycle D n hn) =
      D.cycleOfFiber n hn := by
  exact (additiveCodeFiberSplit D n hn).2.2.2

/-! ## Singleton branch/tensor generator from additive-code data -/

/-- The branch/tensor candidate selected by the terminal split and additive
code. -/
def branchTensorCandidateOfAdditiveCodeData
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7BranchTensorCandidate C n where
  generated := D.generated n hn
  left :=
    D.primitiveAtom
      (additiveCodeLeftCycle D n hn)
      (additiveCodeLeftCycle_primitive D n hn)
  right :=
    D.primitiveAtom
      (additiveCodeRightCycle D n hn)
      (additiveCodeRightCycle_primitive D n hn)
  allowed := D.generated_allowed n hn

/-- The explicit singleton generator induced by additive-code data. -/
def branchTensorGeneratorOfAdditiveCodeData
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    SU7BranchTensorGenerator C where
  candidates n hn := [branchTensorCandidateOfAdditiveCodeData D n hn]

/-! ## Completeness / hit theorem -/

/-- The generated candidate has zero color trace. -/
theorem branchTensorCandidateOfAdditiveCodeData_colorTrace_zero
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    colorTraceResidual
        (branchTensorCandidateOfAdditiveCodeData D n hn).toSameCarrierCell =
      0 := by
  rw [branchTensorCandidate_colorTrace_eq_generated]
  exact D.generated_trace_zero n hn

/-- The generated candidate has zero endpoint residual because the terminal
split's two primitive codes add back to the active fiber code `2*n`. -/
theorem branchTensorCandidateOfAdditiveCodeData_endpointResidual_zero
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    endpointBalanceResidual
        (branchTensorCandidateOfAdditiveCodeData D n hn).toSameCarrierCell =
      0 := by
  rw [branchTensorCandidate_endpointResidual_eq_codes]
  have hbalance :
      (branchTensorCandidateOfAdditiveCodeData D n hn).left.weight.code +
          (branchTensorCandidateOfAdditiveCodeData D n hn).right.weight.code =
        2 * n := by
    calc
      (branchTensorCandidateOfAdditiveCodeData D n hn).left.weight.code +
          (branchTensorCandidateOfAdditiveCodeData D n hn).right.weight.code =
        D.cycleCode (additiveCodeLeftCycle D n hn) +
          D.cycleCode (additiveCodeRightCycle D n hn) := by
            change
              (D.primitiveAtom
                    (additiveCodeLeftCycle D n hn)
                    (additiveCodeLeftCycle_primitive D n hn)).weight.code +
                  (D.primitiveAtom
                    (additiveCodeRightCycle D n hn)
                    (additiveCodeRightCycle_primitive D n hn)).weight.code =
                D.cycleCode (additiveCodeLeftCycle D n hn) +
                  D.cycleCode (additiveCodeRightCycle D n hn)
            rw [D.primitiveAtom_code
              (additiveCodeLeftCycle D n hn)
              (additiveCodeLeftCycle_primitive D n hn)]
            rw [D.primitiveAtom_code
              (additiveCodeRightCycle D n hn)
              (additiveCodeRightCycle_primitive D n hn)]
      _ = D.cycleCode
          (S.glue (additiveCodeLeftCycle D n hn)
            (additiveCodeRightCycle D n hn)) := by
            exact
              (D.glue_code_add
                (additiveCodeLeftCycle_primitive D n hn)
                (additiveCodeRightCycle_primitive D n hn)).symm
      _ = D.cycleCode (D.cycleOfFiber n hn) := by
            rw [additiveCodeGlue_eq_cycle D n hn]
      _ = 2 * n := D.cycleOfFiber_code n hn
  omega

/-- THEOREM 1: the additive-code branch/tensor candidate has full zero
residual. -/
theorem branchTensorCandidateOfAdditiveCodeData_residual_zero
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S)
    (n : ℕ) (hn : 2 ≤ n) :
    (branchTensorCandidateOfAdditiveCodeData D n hn).residual = (0, 0) := by
  unfold SU7BranchTensorCandidate.residual fullCarrierResidual
  apply Prod.ext
  · exact branchTensorCandidateOfAdditiveCodeData_colorTrace_zero D n hn
  · exact branchTensorCandidateOfAdditiveCodeData_endpointResidual_zero D n hn

/-- THEOREM 2: the singleton generator induced by additive-code data hits zero
residual at every active fiber. -/
theorem branchTensorGeneratorOfAdditiveCodeData_hits
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      ∃ cand ∈ (branchTensorGeneratorOfAdditiveCodeData D).candidates n hn,
        cand.residual = (0, 0) := by
  intro n hn
  refine
    ⟨branchTensorCandidateOfAdditiveCodeData D n hn, ?_, ?_⟩
  · simp [branchTensorGeneratorOfAdditiveCodeData]
  · exact branchTensorCandidateOfAdditiveCodeData_residual_zero D n hn

/-- THEOREM 3: additive-code data supplies the explicit P1026
branch/tensor-generator completeness theorem, hence a P1016 lift producer. -/
theorem su7TensorAtomLiftProducer_of_additiveCodeBranchTensorGenerator
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_branchTensorGeneratorHits
    (branchTensorGeneratorOfAdditiveCodeData D)
    (branchTensorGeneratorOfAdditiveCodeData_hits D)

/-! ## Certificate -/

/-- P1028 certificate: P1019 additive-code data constructs an explicit
branch/tensor generator and proves its P1026 hit theorem. -/
structure AdditiveCodeBranchTensorGeneratorCertificate where
  generator :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      DirectedCycleAdditiveCodeData C S -> SU7BranchTensorGenerator C
  hits :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace}
      (D : DirectedCycleAdditiveCodeData C S),
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        ∃ cand ∈
          (branchTensorGeneratorOfAdditiveCodeData D).candidates n hn,
          cand.residual = (0, 0)
  additive_code_to_lift_producer :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      DirectedCycleAdditiveCodeData C S -> SU7TensorAtomLiftProducer C

/-- Canonical P1028 certificate. -/
def additiveCodeBranchTensorGeneratorCertificate :
    AdditiveCodeBranchTensorGeneratorCertificate where
  generator := branchTensorGeneratorOfAdditiveCodeData
  hits := branchTensorGeneratorOfAdditiveCodeData_hits
  additive_code_to_lift_producer :=
    su7TensorAtomLiftProducer_of_additiveCodeBranchTensorGenerator


end StandardModelConstraint
end SaturationMonoid
