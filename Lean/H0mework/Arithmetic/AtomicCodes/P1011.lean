import H0mework.Arithmetic.AtomicCodes.P1009

/-!
# Proposition 1011: same-carrier tensor-atomic cells replace the placeholder

P1005 installed the real same-carrier irreducibility predicate as tensor
indecomposability.  This file turns that predicate into the actual cell shape
for the endpoint producer.

The object below stores no downstream arithmetic witness, no downstream
prime-edge loop, and no ordinary even-coverage statement.  It also does not use the older
`IsIrreducibleRepresentation := True` field.  Its atom proofs are exactly the
same-carrier tensor atomicity proofs from P1005.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Tensor-atomic same-carrier cells -/

/-- Same-carrier endpoint producer cell with real tensor atomicity in the
cell itself.

This is the refined replacement for any path that tries to use the older
placeholder `IsIrreducibleRepresentation` field. -/
structure SU7SameCarrierTensorAtomicCell
    (C : SameCarrierWeightTensorCoding) (n : ℕ) where
  generated : SU7GeneratedTerminalColorCell n
  leftAtom : SameCarrierSU7Atom
  rightAtom : SameCarrierSU7Atom
  left_tensor_atomic : SameCarrierTensorAtomAtomic C leftAtom
  right_tensor_atomic : SameCarrierTensorAtomAtomic C rightAtom
  atom_left_matches_weight :
    SameCarrierAtomMatchesWeight leftAtom generated.leftWeight
  atom_right_matches_weight :
    SameCarrierAtomMatchesWeight rightAtom generated.rightWeight
  allowed : SameCarrierGaugeAllowed generated

/-- Forget only the tensor-atomic proofs, leaving the older same-carrier
endpoint cell. -/
def sameCarrierCellOfTensorAtomicCell
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierTensorAtomicCell C n) :
    SU7SameCarrierAtomicCell n where
  generated := cell.generated
  leftAtom := cell.leftAtom
  rightAtom := cell.rightAtom
  atom_left_matches_weight := cell.atom_left_matches_weight
  atom_right_matches_weight := cell.atom_right_matches_weight
  allowed := cell.allowed

/-- Full residual readout of a tensor-atomic same-carrier cell. -/
def fullCarrierResidualOfTensorAtomicCell
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierTensorAtomicCell C n) : ℤ × ℤ :=
  fullCarrierResidual (sameCarrierCellOfTensorAtomicCell cell)

/-- Tensor-atomic same-carrier zero: the refined cell has zero color trace and
zero endpoint balance.  Atomicity is carried by the cell fields, not by a
downstream readout. -/
def SameCarrierTensorAtomicCellZero
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierTensorAtomicCell C n) : Prop :=
  fullCarrierResidualOfTensorAtomicCell cell = (0, 0)

/-! ## Equivalence with the P1005 tensor-zero gate -/

/-- A refined tensor-atomic cell with full residual zero gives the P1005
tensor-atomic zero gate after forgetting proof fields. -/
theorem tensorAtomicCellZero_to_tensorAtomicZero
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierTensorAtomicCell C n)
    (hzero : SameCarrierTensorAtomicCellZero cell) :
    SameCarrierTensorAtomicZero C
      (sameCarrierCellOfTensorAtomicCell cell) := by
  unfold SameCarrierTensorAtomicCellZero
    fullCarrierResidualOfTensorAtomicCell fullCarrierResidual at hzero
  have htrace : colorTraceResidual
      (sameCarrierCellOfTensorAtomicCell cell) = 0 :=
    congrArg Prod.fst hzero
  have hendpoint : endpointBalanceResidual
      (sameCarrierCellOfTensorAtomicCell cell) = 0 :=
    congrArg Prod.snd hzero
  exact ⟨htrace, hendpoint, cell.left_tensor_atomic,
    cell.right_tensor_atomic⟩

/-- A P1005 tensor-atomic zero gate can be repackaged as the refined cell
shape. -/
def tensorAtomicCellOfTensorAtomicZero
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierAtomicCell n)
    (hzero : SameCarrierTensorAtomicZero C cell) :
    SU7SameCarrierTensorAtomicCell C n where
  generated := cell.generated
  leftAtom := cell.leftAtom
  rightAtom := cell.rightAtom
  left_tensor_atomic := hzero.2.2.1
  right_tensor_atomic := hzero.2.2.2
  atom_left_matches_weight := cell.atom_left_matches_weight
  atom_right_matches_weight := cell.atom_right_matches_weight
  allowed := cell.allowed

/-- Repackaging a P1005 tensor-atomic zero gate preserves full residual zero.
-/
theorem tensorAtomicCellOfTensorAtomicZero_zero
    {C : SameCarrierWeightTensorCoding} {n : ℕ}
    (cell : SU7SameCarrierAtomicCell n)
    (hzero : SameCarrierTensorAtomicZero C cell) :
    SameCarrierTensorAtomicCellZero
      (tensorAtomicCellOfTensorAtomicZero cell hzero) := by
  unfold SameCarrierTensorAtomicCellZero fullCarrierResidualOfTensorAtomicCell
    fullCarrierResidual sameCarrierCellOfTensorAtomicCell
  exact Prod.ext hzero.1 hzero.2.1

/-- The refined tensor-atomic cell fiber is exactly the P1005 tensor-zero
fiber. -/
theorem existsTensorAtomicCellZero_iff_existsTensorAtomicZero
    (C : SameCarrierWeightTensorCoding) {n : ℕ} :
    (∃ cell : SU7SameCarrierTensorAtomicCell C n,
        SameCarrierTensorAtomicCellZero cell) ↔
      ∃ cell : SU7SameCarrierAtomicCell n,
        SameCarrierTensorAtomicZero C cell := by
  constructor
  · rintro ⟨cell, hzero⟩
    exact ⟨sameCarrierCellOfTensorAtomicCell cell,
      tensorAtomicCellZero_to_tensorAtomicZero cell hzero⟩
  · rintro ⟨cell, hzero⟩
    exact ⟨tensorAtomicCellOfTensorAtomicZero cell hzero,
      tensorAtomicCellOfTensorAtomicZero_zero cell hzero⟩

/-! ## The naive `(n,n)` candidate still cannot lift -/

/-- The P1001 `(n,n)` candidate at fiber `4` cannot be upgraded to the
refined tensor-atomic cell shape. -/
theorem no_tensorAtomicLift_of_candidate_four
    (C : SameCarrierWeightTensorCoding) :
    ¬ ∃ cell : SU7SameCarrierTensorAtomicCell C 4,
        sameCarrierCellOfTensorAtomicCell cell =
          sameCarrierAtomicZeroCandidate 4 := by
  rintro ⟨cell, hcell⟩
  have hleft :
      SameCarrierAtomAtomic
        (sameCarrierAtomicZeroCandidate 4).leftAtom := by
    have hleftEq :
        cell.leftAtom = (sameCarrierAtomicZeroCandidate 4).leftAtom := by
      exact congrArg SU7SameCarrierAtomicCell.leftAtom hcell
    have htensor :
        SameCarrierTensorAtomAtomic C
          (sameCarrierAtomicZeroCandidate 4).leftAtom := by
      simpa [hleftEq] using cell.left_tensor_atomic
    exact (sameCarrierTensorAtomAtomic_iff_atomAtomic C
      (sameCarrierAtomicZeroCandidate 4).leftAtom).mp htensor
  exact not_sameCarrierAtomAtomic_candidate_left_four hleft

/-! ## Certificate -/

/-- P1011 certificate: the main same-carrier endpoint object now uses tensor
atomicity directly, and the old `(n,n)` candidate cannot be lifted into it. -/
structure SameCarrierTensorAtomicCellReplacementCertificate where
  to_tensor_zero :
    ∀ {C : SameCarrierWeightTensorCoding} {n : ℕ}
      (cell : SU7SameCarrierTensorAtomicCell C n),
      SameCarrierTensorAtomicCellZero cell ->
        SameCarrierTensorAtomicZero C
          (sameCarrierCellOfTensorAtomicCell cell)
  from_tensor_zero :
    ∀ {C : SameCarrierWeightTensorCoding} {n : ℕ}
      (cell : SU7SameCarrierAtomicCell n),
      SameCarrierTensorAtomicZero C cell ->
        SU7SameCarrierTensorAtomicCell C n
  fiber_equiv :
    ∀ (C : SameCarrierWeightTensorCoding) {n : ℕ},
      (∃ cell : SU7SameCarrierTensorAtomicCell C n,
          SameCarrierTensorAtomicCellZero cell) ↔
        ∃ cell : SU7SameCarrierAtomicCell n,
          SameCarrierTensorAtomicZero C cell
  candidate_four_not_liftable :
    ∀ C : SameCarrierWeightTensorCoding,
      ¬ ∃ cell : SU7SameCarrierTensorAtomicCell C 4,
          sameCarrierCellOfTensorAtomicCell cell =
            sameCarrierAtomicZeroCandidate 4

/-- THEOREM 1: canonical replacement certificate. -/
def sameCarrierTensorAtomicCellReplacementCertificate :
    SameCarrierTensorAtomicCellReplacementCertificate where
  to_tensor_zero := tensorAtomicCellZero_to_tensorAtomicZero
  from_tensor_zero := tensorAtomicCellOfTensorAtomicZero
  fiber_equiv := existsTensorAtomicCellZero_iff_existsTensorAtomicZero
  candidate_four_not_liftable := no_tensorAtomicLift_of_candidate_four


end StandardModelConstraint
end SaturationMonoid
