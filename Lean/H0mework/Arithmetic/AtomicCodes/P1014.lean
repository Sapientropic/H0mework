import H0mework.Arithmetic.AtomicCodes.P1011
import H0mework.Arithmetic.AtomicCodes.PrimeEdgeCore

/-!
# Proposition 1014: SU(7) tensor irreducibility lifts to same-carrier atoms

P1011 gave the endpoint producer its refined same-carrier tensor-atomic cell.
P1013 proved the projection from that tensor atomicity to endpoint primality.

This file connects the representation side back into the refined same-carrier
cell: a `SU7TensorIrreducibleAtom` from P906Core canonically becomes a
same-carrier atom whose tensor atomicity is inherited from the SU(7) tensor
irreducibility proof.

The construction does not produce an endpoint-zero inhabitant for every fiber.
It lowers the remaining producer debt to the right place: generate two SU(7)
tensor-irreducible atoms whose same-carrier endpoint balance vanishes.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Pulling SU(7) tensor coding onto same-carrier endpoint weights -/

/-- Same-carrier tensor coding induced by a SU(7) weight tensor coding.

The block-weight coordinate is transported on the left endpoint; the endpoint
code coordinate is transported by the SU(7) tensor-code law.  The only role of
the block coordinate here is to keep the same-carrier atom matched to the
generated SU(7) terminal cell. -/
def sameCarrierTensorCodingOfSU7
    (C : SU7WeightTensorCoding) :
    SameCarrierWeightTensorCoding where
  tensor u v :=
    { blockWeight := u.blockWeight
      endpointCode :=
        (C.tensor { code := u.endpointCode } { code := v.endpointCode }).code }
  tensor_endpointCode := by
    intro u v
    exact C.tensor_code_mul
      { code := u.endpointCode } { code := v.endpointCode }
  lift_endpoint_factorization := by
    intro w a b hfactor
    refine
      ⟨{ blockWeight := w.blockWeight, endpointCode := a },
        { blockWeight := fun _ => 0, endpointCode := b },
        ?_, rfl, rfl⟩
    cases w with
    | mk blockWeight endpointCode =>
        simp at hfactor ⊢
        simpa [C.tensor_code_mul] using hfactor.symm

/-- A SU(7) tensor-irreducible weight becomes a same-carrier tensor-atomic
atom after choosing the generated terminal block-weight coordinate. -/
theorem sameCarrierTensorAtomAtomic_of_su7TensorIrreducible
    (C : SU7WeightTensorCoding)
    (blockWeight : Fin 7 -> ℤ)
    {w : SU7WeightLattice}
    (hirr : SU7TensorIrreducible C w) :
    SameCarrierTensorAtomAtomic
      (sameCarrierTensorCodingOfSU7 C)
      (sameCarrierAtomOfWeightAndCode blockWeight w.code) := by
  unfold SameCarrierTensorAtomAtomic SameCarrierTensorIrreducible
  constructor
  · exact hirr.1
  · intro u v htensor
    have hcode :
        (C.tensor { code := u.endpointCode }
            { code := v.endpointCode }).code = w.code := by
      simpa [sameCarrierTensorCodingOfSU7,
        sameCarrierAtomOfWeightAndCode] using
        congrArg SameCarrierSU7AtomicWeight.endpointCode htensor
    exact hirr.2 { code := u.endpointCode }
      { code := v.endpointCode } hcode

/-- Convert a P906 tensor-irreducible atom to the same-carrier atom matched to
a chosen generated terminal block-weight. -/
def sameCarrierAtomOfSU7TensorIrreducibleAtom
    {C : SU7WeightTensorCoding}
    (blockWeight : Fin 7 -> ℤ)
    (a : SU7TensorIrreducibleAtom C) :
    SameCarrierSU7Atom :=
  sameCarrierAtomOfWeightAndCode blockWeight a.weight.code

@[simp] theorem sameCarrierAtomOfSU7TensorIrreducibleAtom_matches
    {C : SU7WeightTensorCoding}
    (blockWeight : Fin 7 -> ℤ)
    (a : SU7TensorIrreducibleAtom C) :
    SameCarrierAtomMatchesWeight
      (sameCarrierAtomOfSU7TensorIrreducibleAtom blockWeight a)
      blockWeight := by
  simp [sameCarrierAtomOfSU7TensorIrreducibleAtom]

@[simp] theorem sameCarrierAtomOfSU7TensorIrreducibleAtom_code
    {C : SU7WeightTensorCoding}
    (blockWeight : Fin 7 -> ℤ)
    (a : SU7TensorIrreducibleAtom C) :
    sameCarrierAtomCode
      (sameCarrierAtomOfSU7TensorIrreducibleAtom blockWeight a) =
        a.weight.code := by
  simp [sameCarrierAtomOfSU7TensorIrreducibleAtom]

/-- The converted SU(7) tensor-irreducible atom is tensor-atomic on the
same-carrier coding induced by the original SU(7) tensor coding. -/
theorem sameCarrierAtomOfSU7TensorIrreducibleAtom_tensorAtomic
    {C : SU7WeightTensorCoding}
    (blockWeight : Fin 7 -> ℤ)
    (a : SU7TensorIrreducibleAtom C) :
    SameCarrierTensorAtomAtomic
      (sameCarrierTensorCodingOfSU7 C)
      (sameCarrierAtomOfSU7TensorIrreducibleAtom blockWeight a) := by
  exact sameCarrierTensorAtomAtomic_of_su7TensorIrreducible
    C blockWeight a.tensor_irreducible

/-! ## Same-carrier cell built from SU(7) tensor atoms -/

/-- Build the P1011 refined same-carrier cell directly from a generated
terminal color cell and two P906 SU(7) tensor-irreducible atoms. -/
def sameCarrierTensorAtomicCellOfSU7TensorAtoms
    {C : SU7WeightTensorCoding} {n : ℕ}
    (generated : SU7GeneratedTerminalColorCell n)
    (left right : SU7TensorIrreducibleAtom C)
    (allowed : SameCarrierGaugeAllowed generated) :
    SU7SameCarrierTensorAtomicCell
      (sameCarrierTensorCodingOfSU7 C) n where
  generated := generated
  leftAtom :=
    sameCarrierAtomOfSU7TensorIrreducibleAtom generated.leftWeight left
  rightAtom :=
    sameCarrierAtomOfSU7TensorIrreducibleAtom generated.rightWeight right
  left_tensor_atomic :=
    sameCarrierAtomOfSU7TensorIrreducibleAtom_tensorAtomic
      generated.leftWeight left
  right_tensor_atomic :=
    sameCarrierAtomOfSU7TensorIrreducibleAtom_tensorAtomic
      generated.rightWeight right
  atom_left_matches_weight := by
    simp [sameCarrierAtomOfSU7TensorIrreducibleAtom]
  atom_right_matches_weight := by
    simp [sameCarrierAtomOfSU7TensorIrreducibleAtom]
  allowed := allowed

/-- Endpoint balance of the lifted same-carrier cell is exactly the sum of
the two SU(7) tensor-atom weight codes. -/
theorem endpointBalanceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms
    {C : SU7WeightTensorCoding} {n : ℕ}
    (generated : SU7GeneratedTerminalColorCell n)
    (left right : SU7TensorIrreducibleAtom C)
    (allowed : SameCarrierGaugeAllowed generated) :
    endpointBalanceResidual
        (sameCarrierCellOfTensorAtomicCell
          (sameCarrierTensorAtomicCellOfSU7TensorAtoms
            generated left right allowed)) =
      ((left.weight.code : ℤ) + (right.weight.code : ℤ)) -
        ((2 * n : ℕ) : ℤ) := by
  simp [endpointBalanceResidual,
    sameCarrierTensorAtomicCellOfSU7TensorAtoms,
    sameCarrierCellOfTensorAtomicCell,
    sameCarrierAtomOfSU7TensorIrreducibleAtom]

/-- The lifted cell has tensor-atomic endpoints by construction; zero is
therefore reduced to generated color trace plus the SU(7) atom-code balance.
-/
theorem sameCarrierTensorAtomicCellOfSU7TensorAtoms_zero_of_trace_and_balance
    {C : SU7WeightTensorCoding} {n : ℕ}
    (generated : SU7GeneratedTerminalColorCell n)
    (left right : SU7TensorIrreducibleAtom C)
    (allowed : SameCarrierGaugeAllowed generated)
    (htrace :
      colorTraceResidual
        (sameCarrierCellOfTensorAtomicCell
          (sameCarrierTensorAtomicCellOfSU7TensorAtoms
            generated left right allowed)) = 0)
    (hbalance :
      left.weight.code + right.weight.code = 2 * n) :
    SameCarrierTensorAtomicCellZero
      (sameCarrierTensorAtomicCellOfSU7TensorAtoms
        generated left right allowed) := by
  unfold SameCarrierTensorAtomicCellZero fullCarrierResidualOfTensorAtomicCell
    fullCarrierResidual
  apply Prod.ext
  · exact htrace
  · rw [endpointBalanceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms]
    omega

/-! ## Certificate -/

/-- P1014 certificate: the P1011 same-carrier tensor-atomic cell can be built
from actual P906 SU(7) tensor-irreducible atoms. -/
structure SU7TensorIrreducibleSameCarrierLiftCertificate where
  induced_coding :
    SU7WeightTensorCoding -> SameCarrierWeightTensorCoding
  tensor_irreducible_to_same_carrier_atomic :
    ∀ (C : SU7WeightTensorCoding) (blockWeight : Fin 7 -> ℤ)
      {w : SU7WeightLattice},
      SU7TensorIrreducible C w ->
        SameCarrierTensorAtomAtomic
          (sameCarrierTensorCodingOfSU7 C)
          (sameCarrierAtomOfWeightAndCode blockWeight w.code)
  atom_lift :
    ∀ {C : SU7WeightTensorCoding},
      (Fin 7 -> ℤ) -> SU7TensorIrreducibleAtom C -> SameCarrierSU7Atom
  atom_lift_tensor_atomic :
    ∀ {C : SU7WeightTensorCoding}
      (blockWeight : Fin 7 -> ℤ) (a : SU7TensorIrreducibleAtom C),
      SameCarrierTensorAtomAtomic
        (sameCarrierTensorCodingOfSU7 C)
        (sameCarrierAtomOfSU7TensorIrreducibleAtom blockWeight a)
  cell_lift :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (generated : SU7GeneratedTerminalColorCell n),
      SU7TensorIrreducibleAtom C ->
        SU7TensorIrreducibleAtom C ->
          SameCarrierGaugeAllowed generated ->
            SU7SameCarrierTensorAtomicCell
              (sameCarrierTensorCodingOfSU7 C) n
  zero_of_trace_and_balance :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (generated : SU7GeneratedTerminalColorCell n)
      (left right : SU7TensorIrreducibleAtom C)
      (allowed : SameCarrierGaugeAllowed generated),
      colorTraceResidual
          (sameCarrierCellOfTensorAtomicCell
            (sameCarrierTensorAtomicCellOfSU7TensorAtoms
              generated left right allowed)) = 0 ->
        left.weight.code + right.weight.code = 2 * n ->
          SameCarrierTensorAtomicCellZero
            (sameCarrierTensorAtomicCellOfSU7TensorAtoms
              generated left right allowed)

/-- THEOREM 1: canonical SU(7) tensor-irreducible same-carrier lift
certificate. -/
def su7TensorIrreducibleSameCarrierLiftCertificate :
    SU7TensorIrreducibleSameCarrierLiftCertificate where
  induced_coding := sameCarrierTensorCodingOfSU7
  tensor_irreducible_to_same_carrier_atomic :=
    sameCarrierTensorAtomAtomic_of_su7TensorIrreducible
  atom_lift := sameCarrierAtomOfSU7TensorIrreducibleAtom
  atom_lift_tensor_atomic :=
    sameCarrierAtomOfSU7TensorIrreducibleAtom_tensorAtomic
  cell_lift := sameCarrierTensorAtomicCellOfSU7TensorAtoms
  zero_of_trace_and_balance :=
    sameCarrierTensorAtomicCellOfSU7TensorAtoms_zero_of_trace_and_balance


end StandardModelConstraint
end SaturationMonoid
