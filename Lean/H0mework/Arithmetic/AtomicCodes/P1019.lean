import H0mework.Arithmetic.AtomicCodes.P1018

/-!
# Proposition 1019: residual split atomicity is read through one additive code

P1018 still stored the endpoint-balance law as a semantic field of
`DirectedCycleSameCarrierRealization`.  This file lowers that receipt one
level.  The upstream producer now supplies:

* closed terminal cycles over each active fiber;
* the P1017 descent law, which splits such a cycle into two primitive cycles;
* one carrier code on directed cycles;
* additivity of that code under the primitive glue;
* realization of each primitive cycle as a SU(7) tensor-irreducible atom whose
  endpoint code is the carrier code.

So the endpoint balance is no longer stored.  It is computed from the same
carrier readout:

```text
code(A) + code(B) = code(glue A B) = code(C_n) = 2*n
```

This is the Lean throat for the “terminal residual split leaves only atomic
faces” idea: terminality produces the two primitive faces, and the single
additive carrier code makes their endpoint balance a theorem rather than an
extra assumption.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Additive-code realization of terminal residual splits -/

/-- A directed-cycle realization where endpoint balance is derived from a
single additive carrier code, rather than stored as a separate balance field.

The primitive cycles are the keep / trace faces of the terminal residual split.
Their tensor-irreducible SU(7) atom realization is still upstream of any
arithmetic projection. -/
structure DirectedCycleAdditiveCodeData
    (C : SU7WeightTensorCoding)
    (S : DirectedCycleDescentSpace) where
  cycleOfFiber : (n : ℕ) -> 2 ≤ n -> DirectedCycle
  cycle_even :
    ∀ (n : ℕ) (hn : 2 ≤ n), Even (cycleOfFiber n hn).length
  cycle_closed :
    ∀ (n : ℕ) (hn : 2 ≤ n), (cycleOfFiber n hn).holonomy = 0
  cycle_terminal :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      TerminalUnderDescent S (cycleOfFiber n hn)
  generated :
    (n : ℕ) -> 2 ≤ n -> SU7GeneratedTerminalColorCell n
  generated_allowed :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      SameCarrierGaugeAllowed (generated n hn)
  generated_trace_zero :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell (generated n hn)) = 0
  cycleCode : DirectedCycle -> ℕ
  cycleOfFiber_code :
    ∀ (n : ℕ) (hn : 2 ≤ n), cycleCode (cycleOfFiber n hn) = 2 * n
  glue_code_add :
    ∀ {A B : DirectedCycle},
      PrimitiveCycle A ->
        PrimitiveCycle B ->
          cycleCode (S.glue A B) = cycleCode A + cycleCode B
  primitiveAtom :
    (P : DirectedCycle) -> PrimitiveCycle P -> SU7TensorIrreducibleAtom C
  primitiveAtom_code :
    ∀ (P : DirectedCycle) (hP : PrimitiveCycle P),
      (primitiveAtom P hP).weight.code = cycleCode P

/-! ## Additive code derives the P1018 balance law -/

/-- Additive carrier-code data derives the P1018 realization; the endpoint
balance is computed from the glue-code law. -/
def directedCycleSameCarrierRealization_of_additiveCodeData
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    DirectedCycleSameCarrierRealization C S := by
  refine
    { cycleOfFiber := D.cycleOfFiber
      cycle_even := D.cycle_even
      cycle_closed := D.cycle_closed
      cycle_terminal := D.cycle_terminal
      generated := D.generated
      generated_allowed := D.generated_allowed
      generated_trace_zero := D.generated_trace_zero
      primitiveAtom := D.primitiveAtom
      primitive_glue_code_balance := ?_ }
  intro n hn A B hA hB hglue
  calc
    (D.primitiveAtom A hA).weight.code +
        (D.primitiveAtom B hB).weight.code =
      D.cycleCode A + D.cycleCode B := by
        rw [D.primitiveAtom_code A hA, D.primitiveAtom_code B hB]
    _ = D.cycleCode (S.glue A B) := by
        exact (D.glue_code_add hA hB).symm
    _ = D.cycleCode (D.cycleOfFiber n hn) := by
        rw [hglue]
    _ = 2 * n := D.cycleOfFiber_code n hn

/-- Additive residual-split code data feeds the same-carrier tensor-atom lift
producer. -/
theorem su7TensorAtomLiftProducer_of_additiveCodeData
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_directedCycleRealization
    (directedCycleSameCarrierRealization_of_additiveCodeData D)

/-- Additive residual-split code data inherits the unbounded primitive-code
constraint. -/
theorem directedCycleAdditiveCodeData_forces_unboundedPrimitiveCodes
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : DirectedCycleAdditiveCodeData C S) :
    ∀ bound : ℕ,
      ∃ (n : ℕ) (hn : 2 ≤ n) (A B : DirectedCycle)
        (hA : PrimitiveCycle A) (hB : PrimitiveCycle B),
        bound < n ∧
          S.glue A B = D.cycleOfFiber n hn ∧
            (bound < (D.primitiveAtom A hA).weight.code ∨
              bound < (D.primitiveAtom B hB).weight.code) := by
  intro bound
  rcases
    directedCycleSameCarrierRealization_forces_unboundedPrimitiveCodes
      (directedCycleSameCarrierRealization_of_additiveCodeData D) bound with
    ⟨n, hn, A, B, hA, hB, hgt, hglue, hlarge⟩
  exact ⟨n, hn, A, B, hA, hB, hgt, hglue, hlarge⟩

/-! ## Certificate -/

/-- P1019 certificate: terminal residual split plus one additive carrier code
derives the same-carrier endpoint producer. -/
structure DirectedCycleAdditiveCodeProducerCertificate where
  additive_code_to_realization :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      DirectedCycleAdditiveCodeData C S ->
        DirectedCycleSameCarrierRealization C S
  additive_code_to_lift_producer :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      DirectedCycleAdditiveCodeData C S ->
        SU7TensorAtomLiftProducer C
  additive_code_forces_unbounded_codes :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      (D : DirectedCycleAdditiveCodeData C S) ->
        ∀ bound : ℕ,
          ∃ (n : ℕ) (hn : 2 ≤ n) (A B : DirectedCycle)
            (hA : PrimitiveCycle A) (hB : PrimitiveCycle B),
            bound < n ∧
              S.glue A B = D.cycleOfFiber n hn ∧
                (bound < (D.primitiveAtom A hA).weight.code ∨
                  bound < (D.primitiveAtom B hB).weight.code)

/-- Canonical P1019 certificate. -/
def directedCycleAdditiveCodeProducerCertificate :
    DirectedCycleAdditiveCodeProducerCertificate := by
  constructor
  · intro C S D
    exact directedCycleSameCarrierRealization_of_additiveCodeData D
  · intro C S D
    exact su7TensorAtomLiftProducer_of_additiveCodeData D
  · intro C S D
    exact directedCycleAdditiveCodeData_forces_unboundedPrimitiveCodes D


end StandardModelConstraint
end SaturationMonoid
