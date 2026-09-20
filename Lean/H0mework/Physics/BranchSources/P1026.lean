import H0mework.Arithmetic.AtomicCodes.P1019

/-!
# Proposition 1026: SU(7) branch/tensor generator soundness

The current first hard gate is an inhabitant producer:

```lean
forall n, 2 <= n ->
  exists cell : SU7SameCarrierAtomicCell n,
    SameCarrierTensorAtomicZero C cell
```

P1014/P1018/P1019 lower the problem to the right objects, but they are still
interfaces.  This file introduces the explicit upstream generator surface that
the real producer must inhabit:

* a branch/tensor candidate is a generated SU(7) terminal color cell plus two
  SU(7) tensor-irreducible atoms and the gauge-allowed proof;
* it stores no endpoint atomicity field, no prime proof, no Goldbach object,
  and no target equality;
* its residual is computed after lifting into the same-carrier cell.

The theorem proved here is only soundness: a candidate whose computed
same-carrier residual is zero becomes a `SameCarrierTensorAtomicZero` cell.
Completeness is intentionally not baked in as a structure field.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Branch/tensor generator candidates -/

/-- A raw SU(7) branch/tensor candidate for a single active fiber.

The candidate contains only upstream generator material: generated color cell,
two tensor-irreducible atoms, and gauge allowance.  It does not store a zero
proof, endpoint atomicity proof, prime proof, or arithmetic projection. -/
structure SU7BranchTensorCandidate
    (C : SU7WeightTensorCoding) (n : ℕ) where
  generated : SU7GeneratedTerminalColorCell n
  left : SU7TensorIrreducibleAtom C
  right : SU7TensorIrreducibleAtom C
  allowed : SameCarrierGaugeAllowed generated

/-- Lift a branch/tensor candidate to the refined same-carrier tensor-atomic
cell from P1014. -/
def SU7BranchTensorCandidate.toTensorAtomicCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n) :
    SU7SameCarrierTensorAtomicCell
      (sameCarrierTensorCodingOfSU7 C) n :=
  sameCarrierTensorAtomicCellOfSU7TensorAtoms
    cand.generated cand.left cand.right cand.allowed

/-- Forget only the tensor-atomic proof fields, exposing the older
same-carrier cell readout. -/
def SU7BranchTensorCandidate.toSameCarrierCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n) :
    SU7SameCarrierAtomicCell n :=
  sameCarrierCellOfTensorAtomicCell cand.toTensorAtomicCell

/-- The computed residual of a branch/tensor candidate on the same carrier. -/
def SU7BranchTensorCandidate.residual
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n) : ℤ × ℤ :=
  fullCarrierResidual cand.toSameCarrierCell

/-- A generator is a finite candidate list for each active fiber.

The list may be empty; completeness is a theorem to prove about a concrete
generator, not a field stored here. -/
structure SU7BranchTensorGenerator
    (C : SU7WeightTensorCoding) where
  candidates :
    ∀ n : ℕ, 2 ≤ n -> List (SU7BranchTensorCandidate C n)

/-! ## Soundness -/

/-- Candidate residual zero is exactly full residual zero of the lifted
same-carrier tensor-atomic cell. -/
theorem branchTensorCandidate_zero_to_tensorAtomicCellZero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n)
    (hzero : cand.residual = (0, 0)) :
    SameCarrierTensorAtomicCellZero cand.toTensorAtomicCell := by
  exact hzero

/-- Candidate residual zero gives the P1005 tensor-atomic zero gate after
forgetting the tensor proof fields. -/
theorem branchTensorCandidate_zero_to_tensorAtomicZero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n)
    (hzero : cand.residual = (0, 0)) :
    SameCarrierTensorAtomicZero
      (sameCarrierTensorCodingOfSU7 C)
      cand.toSameCarrierCell :=
  tensorAtomicCellZero_to_tensorAtomicZero
    cand.toTensorAtomicCell
    (branchTensorCandidate_zero_to_tensorAtomicCellZero cand hzero)

/-- If a generator emits a zero-residual candidate at every active fiber, then
it supplies the P1016 lift producer.

The hypothesis is the exact remaining completeness theorem.  It is not stored
inside the generator and is not discharged here. -/
theorem su7TensorAtomLiftProducer_of_branchTensorGeneratorHits
    {C : SU7WeightTensorCoding}
    (G : SU7BranchTensorGenerator C)
    (hits :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        ∃ cand ∈ G.candidates n hn, cand.residual = (0, 0)) :
    SU7TensorAtomLiftProducer C := by
  intro n hn
  rcases hits n hn with ⟨cand, _hmem, hzero⟩
  refine
    ⟨cand.generated, cand.left, cand.right, cand.allowed, ?_⟩
  exact branchTensorCandidate_zero_to_tensorAtomicCellZero cand hzero

/-! ## Residual readout formulae -/

/-- The color trace readout of a candidate is the generated physical color
trace. -/
theorem branchTensorCandidate_colorTrace_eq_generated
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n) :
    colorTraceResidual cand.toSameCarrierCell =
      physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell cand.generated) := by
  exact
    colorTraceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms
      cand.generated cand.left cand.right cand.allowed

/-- The endpoint-balance residual of a candidate is computed from the two
SU(7) tensor-atom codes. -/
theorem branchTensorCandidate_endpointResidual_eq_codes
    {C : SU7WeightTensorCoding} {n : ℕ}
    (cand : SU7BranchTensorCandidate C n) :
    endpointBalanceResidual cand.toSameCarrierCell =
      ((cand.left.weight.code : ℤ) + (cand.right.weight.code : ℤ)) -
        ((2 * n : ℕ) : ℤ) := by
  exact
    endpointBalanceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms
      cand.generated cand.left cand.right cand.allowed

/-! ## Certificate -/

/-- P1026 certificate: the explicit SU(7) branch/tensor generator surface is
sound, and the only remaining theorem is generator hit/completeness. -/
structure SU7BranchTensorGeneratorSoundnessCertificate where
  candidate_to_tensor_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7BranchTensorCandidate C n ->
        SU7SameCarrierTensorAtomicCell
          (sameCarrierTensorCodingOfSU7 C) n
  zero_to_tensor_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (cand : SU7BranchTensorCandidate C n),
      cand.residual = (0, 0) ->
        SameCarrierTensorAtomicZero
          (sameCarrierTensorCodingOfSU7 C)
          cand.toSameCarrierCell
  generator_hits_to_lift_producer :
    ∀ {C : SU7WeightTensorCoding}
      (G : SU7BranchTensorGenerator C),
      (∀ n : ℕ, ∀ hn : 2 ≤ n,
        ∃ cand ∈ G.candidates n hn, cand.residual = (0, 0)) ->
          SU7TensorAtomLiftProducer C
  color_trace_formula :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (cand : SU7BranchTensorCandidate C n),
      colorTraceResidual cand.toSameCarrierCell =
        physicalColorLoopTrace
          (terminalPhysicalCellOfGeneratedColorCell cand.generated)
  endpoint_residual_formula :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (cand : SU7BranchTensorCandidate C n),
      endpointBalanceResidual cand.toSameCarrierCell =
        ((cand.left.weight.code : ℤ) + (cand.right.weight.code : ℤ)) -
          ((2 * n : ℕ) : ℤ)

/-- Canonical P1026 soundness certificate. -/
def su7BranchTensorGeneratorSoundnessCertificate :
    SU7BranchTensorGeneratorSoundnessCertificate where
  candidate_to_tensor_cell := fun cand => cand.toTensorAtomicCell
  zero_to_tensor_zero := branchTensorCandidate_zero_to_tensorAtomicZero
  generator_hits_to_lift_producer :=
    su7TensorAtomLiftProducer_of_branchTensorGeneratorHits
  color_trace_formula := branchTensorCandidate_colorTrace_eq_generated
  endpoint_residual_formula := branchTensorCandidate_endpointResidual_eq_codes


end StandardModelConstraint
end SaturationMonoid
