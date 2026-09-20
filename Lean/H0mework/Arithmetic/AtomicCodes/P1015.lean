import H0mework.Arithmetic.AtomicCodes.P1014

/-!
# Proposition 1015: finite SU(7) tensor-atom lift producers cannot be complete

P1014 made the correct representation-side lift:

```text
SU7TensorIrreducibleAtom -> SU7SameCarrierTensorAtomicCell
```

This file proves the next hard constraint on that route.  A producer whose
left/right SU(7) tensor atoms factor through one fixed finite index type
cannot inhabit all active endpoint fibers.  This is the P1009 obstruction
specialized to the actual P1014 lift, so it rules out completing the endpoint
producer by a finite SU(7) incidence table or a fixed finite tensor-atom list.

No downstream arithmetic throat is imported here.  The theorem uses only
same-carrier endpoint codes, tensor atomicity, and boundedness.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Finite SU(7) tensor-atom lift producer shape -/

/-- A P1014-style producer whose left/right SU(7) tensor atoms factor through
one fixed finite index type.

The generated terminal color cell may still depend on the fiber `n`; the
endpoint atoms do not.  This is exactly the "finite incidence/table" route
that P1008/P1009 say cannot be the full endpoint producer. -/
def FiniteSU7TensorAtomLiftProducer
    (C : SU7WeightTensorCoding)
    (ι : Type*) [Fintype ι]
    (generated : ∀ n : ℕ, ι -> SU7GeneratedTerminalColorCell n)
    (left right : ι -> SU7TensorIrreducibleAtom C)
    (allowed : ∀ n : ℕ, ∀ i : ι,
      SameCarrierGaugeAllowed (generated n i)) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ i : ι,
      SameCarrierTensorAtomicCellZero
        (sameCarrierTensorAtomicCellOfSU7TensorAtoms
          (generated n i) (left i) (right i) (allowed n i))

/-- Any finite SU(7) tensor-atom lift producer induces a finite endpoint-indexed
tensor producer. -/
theorem finiteSU7TensorAtomLiftProducer_to_finiteEndpointIndexedTensorProducer
    (C : SU7WeightTensorCoding)
    (ι : Type*) [Fintype ι]
    (generated : ∀ n : ℕ, ι -> SU7GeneratedTerminalColorCell n)
    (left right : ι -> SU7TensorIrreducibleAtom C)
    (allowed : ∀ n : ℕ, ∀ i : ι,
      SameCarrierGaugeAllowed (generated n i))
    (H : FiniteSU7TensorAtomLiftProducer C ι generated left right allowed) :
    FiniteEndpointIndexedTensorProducer
      (sameCarrierTensorCodingOfSU7 C) ι
      (fun i => (left i).weight.code)
      (fun i => (right i).weight.code) := by
  intro n hn
  rcases H n hn with ⟨i, hzero⟩
  let tcell :=
    sameCarrierTensorAtomicCellOfSU7TensorAtoms
      (generated n i) (left i) (right i) (allowed n i)
  refine
    ⟨i, sameCarrierCellOfTensorAtomicCell tcell, ?_, ?_, ?_⟩
  · change
      sameCarrierAtomCode
          (sameCarrierAtomOfSU7TensorIrreducibleAtom
            (generated n i).leftWeight (left i)) =
        (left i).weight.code
    exact sameCarrierAtomOfSU7TensorIrreducibleAtom_code
      (generated n i).leftWeight (left i)
  · change
      sameCarrierAtomCode
          (sameCarrierAtomOfSU7TensorIrreducibleAtom
            (generated n i).rightWeight (right i)) =
        (right i).weight.code
    exact sameCarrierAtomOfSU7TensorIrreducibleAtom_code
      (generated n i).rightWeight (right i)
  · exact tensorAtomicCellZero_to_tensorAtomicZero tcell hzero

/-- No complete P1014 lift producer can factor its SU(7) tensor atoms through
one fixed finite index type. -/
theorem no_finiteSU7TensorAtomLiftProducer
    (C : SU7WeightTensorCoding)
    (ι : Type*) [Fintype ι]
    (generated : ∀ n : ℕ, ι -> SU7GeneratedTerminalColorCell n)
    (left right : ι -> SU7TensorIrreducibleAtom C)
    (allowed : ∀ n : ℕ, ∀ i : ι,
      SameCarrierGaugeAllowed (generated n i)) :
    ¬ FiniteSU7TensorAtomLiftProducer C ι generated left right allowed := by
  intro H
  have hfinite :
      FiniteEndpointIndexedTensorProducer
        (sameCarrierTensorCodingOfSU7 C) ι
        (fun i => (left i).weight.code)
        (fun i => (right i).weight.code) :=
    finiteSU7TensorAtomLiftProducer_to_finiteEndpointIndexedTensorProducer
      C ι generated left right allowed H
  exact no_finiteEndpointIndexedTensorProducer
    (sameCarrierTensorCodingOfSU7 C) ι
    (fun i => (left i).weight.code)
    (fun i => (right i).weight.code)
    hfinite

/-! ## Certificate -/

/-- P1015 certificate: the P1014 lift route is real, but any complete producer
on that route must use an unbounded SU(7) tensor-atom family rather than a
fixed finite table. -/
structure FiniteSU7TensorAtomLiftNoGoCertificate where
  finite_lift_to_finite_endpoint :
    ∀ (C : SU7WeightTensorCoding)
      (ι : Type*) [Fintype ι]
      (generated : ∀ n : ℕ, ι -> SU7GeneratedTerminalColorCell n)
      (left right : ι -> SU7TensorIrreducibleAtom C)
      (allowed : ∀ n : ℕ, ∀ i : ι,
        SameCarrierGaugeAllowed (generated n i)),
      FiniteSU7TensorAtomLiftProducer C ι generated left right allowed ->
        FiniteEndpointIndexedTensorProducer
          (sameCarrierTensorCodingOfSU7 C) ι
          (fun i => (left i).weight.code)
          (fun i => (right i).weight.code)
  no_finite_lift :
    ∀ (C : SU7WeightTensorCoding)
      (ι : Type*) [Fintype ι]
      (generated : ∀ n : ℕ, ι -> SU7GeneratedTerminalColorCell n)
      (left right : ι -> SU7TensorIrreducibleAtom C)
      (allowed : ∀ n : ℕ, ∀ i : ι,
        SameCarrierGaugeAllowed (generated n i)),
      ¬ FiniteSU7TensorAtomLiftProducer C ι generated left right allowed

/-- THEOREM 1: canonical finite SU(7) tensor-atom lift no-go certificate. -/
def finiteSU7TensorAtomLiftNoGoCertificate :
    FiniteSU7TensorAtomLiftNoGoCertificate where
  finite_lift_to_finite_endpoint :=
    finiteSU7TensorAtomLiftProducer_to_finiteEndpointIndexedTensorProducer
  no_finite_lift := no_finiteSU7TensorAtomLiftProducer


end StandardModelConstraint
end SaturationMonoid
