import H0mework.Arithmetic.AtomicCodes.P1016
import H0mework.Realization.Descent.P1017

/-!
# Proposition 1018: cycle-split realization feeds the same-carrier producer

P1017 proved the pure descent theorem:

```text
even + closed + terminal  ->  two primitive cycles glued to the original cycle
```

This file connects that theorem to the current first hard gate without
importing an arithmetic projection.  A realization of directed primitive
cycles as SU(7) tensor-irreducible atoms supplies exactly the data needed by
P1014: the generated color trace is zero and the primitive-glue code balance is
the fiber endpoint balance.

The theorem here is not the final inhabitant producer by itself.  It relocates
the remaining burden to a clean upstream object:

```text
DirectedCycleSameCarrierRealization
```

Once that realization is constructed from the actual ring / color-loop
geometry, Lean produces the P1016 `SU7TensorAtomLiftProducer` directly.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Directed-cycle realization into the same carrier -/

/-- A realization of the directed-cycle descent producer in the SU(7)
same-carrier tensor throat.

The fields are deliberately upstream:

* `cycleOfFiber` gives the ring-space cycle over an active fiber;
* `primitiveAtom` realizes a primitive directed cycle as a tensor-irreducible
  SU(7) atom;
* `primitive_glue_code_balance` is the semantic statement that the closed
  primitive split computes the endpoint balance on the same carrier.

No endpoint atomicity proof, prime-edge object, or downstream arithmetic
statement is stored here. -/
structure DirectedCycleSameCarrierRealization
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
  primitiveAtom :
    (P : DirectedCycle) -> PrimitiveCycle P -> SU7TensorIrreducibleAtom C
  primitive_glue_code_balance :
    ∀ {n : ℕ} {hn : 2 ≤ n} {A B : DirectedCycle}
      (hA : PrimitiveCycle A) (hB : PrimitiveCycle B),
      S.glue A B = cycleOfFiber n hn ->
        (primitiveAtom A hA).weight.code +
          (primitiveAtom B hB).weight.code = 2 * n

/-! ## Realization produces the P1016 lift producer -/

/-- The generated color-trace readout is preserved by the P1014 same-carrier
cell lift. -/
theorem colorTraceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms
    {C : SU7WeightTensorCoding} {n : ℕ}
    (generated : SU7GeneratedTerminalColorCell n)
    (left right : SU7TensorIrreducibleAtom C)
    (allowed : SameCarrierGaugeAllowed generated) :
    colorTraceResidual
        (sameCarrierCellOfTensorAtomicCell
          (sameCarrierTensorAtomicCellOfSU7TensorAtoms
            generated left right allowed)) =
      physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell generated) := by
  rfl

/-- A directed-cycle same-carrier realization is exactly enough to produce the
P1016 SU(7) tensor-atom lift producer. -/
theorem su7TensorAtomLiftProducer_of_directedCycleRealization
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (R : DirectedCycleSameCarrierRealization C S) :
    SU7TensorAtomLiftProducer C := by
  intro n hn
  let cyc := R.cycleOfFiber n hn
  have hsplit :
      ∃ A B : DirectedCycle,
        PrimitiveCycle A ∧ PrimitiveCycle B ∧ S.glue A B = cyc :=
    evenCycle_twoPrimitiveDecomposition S cyc
      (R.cycle_even n hn)
      (R.cycle_closed n hn)
      (R.cycle_terminal n hn)
  rcases hsplit with ⟨A, B, hA, hB, hglue⟩
  let generated := R.generated n hn
  let left := R.primitiveAtom A hA
  let right := R.primitiveAtom B hB
  let allowed := R.generated_allowed n hn
  refine ⟨generated, left, right, allowed, ?_⟩
  apply sameCarrierTensorAtomicCellOfSU7TensorAtoms_zero_of_trace_and_balance
  · rw [colorTraceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms]
    exact R.generated_trace_zero n hn
  · exact R.primitive_glue_code_balance hA hB hglue

/-- Any directed-cycle same-carrier realization strong enough to feed the
endpoint producer must have unbounded primitive-code spectrum.

This is pulled directly from the P1017 split plus the semantic code-balance
law; it rules out replacing the missing realization with a finite primitive
cycle atlas. -/
theorem directedCycleSameCarrierRealization_forces_unboundedPrimitiveCodes
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (R : DirectedCycleSameCarrierRealization C S) :
    ∀ bound : ℕ,
      ∃ (n : ℕ) (hn : 2 ≤ n) (A B : DirectedCycle)
        (hA : PrimitiveCycle A) (hB : PrimitiveCycle B),
        bound < n ∧
          S.glue A B = R.cycleOfFiber n hn ∧
            (bound < (R.primitiveAtom A hA).weight.code ∨
              bound < (R.primitiveAtom B hB).weight.code) := by
  intro bound
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  let cyc := R.cycleOfFiber n hn
  have hsplit :
      ∃ A B : DirectedCycle,
        PrimitiveCycle A ∧ PrimitiveCycle B ∧ S.glue A B = cyc :=
    evenCycle_twoPrimitiveDecomposition S cyc
      (R.cycle_even n hn)
      (R.cycle_closed n hn)
      (R.cycle_terminal n hn)
  rcases hsplit with ⟨A, B, hA, hB, hglue⟩
  have hbalance :
      (R.primitiveAtom A hA).weight.code +
        (R.primitiveAtom B hB).weight.code = 2 * n :=
    R.primitive_glue_code_balance hA hB hglue
  have hlarge :
      bound < (R.primitiveAtom A hA).weight.code ∨
        bound < (R.primitiveAtom B hB).weight.code := by
    omega
  exact ⟨n, hn, A, B, hA, hB, hgt, hglue, hlarge⟩

/-! ## Certificate -/

/-- P1018 certificate: realizing P1017 primitive cycles as SU(7)
tensor-irreducible atoms feeds the same-carrier tensor-atom lift producer. -/
structure DirectedCycleSameCarrierProducerCertificate where
  color_trace_preserved :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (generated : SU7GeneratedTerminalColorCell n)
      (left right : SU7TensorIrreducibleAtom C)
      (allowed : SameCarrierGaugeAllowed generated),
      colorTraceResidual
          (sameCarrierCellOfTensorAtomicCell
            (sameCarrierTensorAtomicCellOfSU7TensorAtoms
              generated left right allowed)) =
        physicalColorLoopTrace
          (terminalPhysicalCellOfGeneratedColorCell generated)
  realization_to_lift_producer :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      DirectedCycleSameCarrierRealization C S ->
        SU7TensorAtomLiftProducer C
  realization_forces_unbounded_codes :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      (R : DirectedCycleSameCarrierRealization C S) ->
        ∀ bound : ℕ,
          ∃ (n : ℕ) (hn : 2 ≤ n) (A B : DirectedCycle)
            (hA : PrimitiveCycle A) (hB : PrimitiveCycle B),
            bound < n ∧
              S.glue A B = R.cycleOfFiber n hn ∧
                (bound < (R.primitiveAtom A hA).weight.code ∨
                  bound < (R.primitiveAtom B hB).weight.code)

/-- Canonical P1018 certificate. -/
theorem directedCycleSameCarrierProducerCertificate :
    DirectedCycleSameCarrierProducerCertificate := by
  constructor
  · intro C n generated left right allowed
    exact
      colorTraceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms
        generated left right allowed
  · intro C S R
    exact su7TensorAtomLiftProducer_of_directedCycleRealization R
  · intro C S R
    exact directedCycleSameCarrierRealization_forces_unboundedPrimitiveCodes R


end StandardModelConstraint
end SaturationMonoid
