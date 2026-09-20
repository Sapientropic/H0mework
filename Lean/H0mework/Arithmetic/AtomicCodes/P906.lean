import H0mework.Arithmetic.AtomicCodes.P905
import H0mework.Arithmetic.AtomicCodes.PrimeEdgeCore

/-!
# Proposition 906: tensor-irreducible branch cells project to prime edges

P905 states the global realization throat:

```text
SU7TensorCodingRealizesIrreducibility C
```

This file supplies a more local producer shape.  Instead of asking the
placeholder `IsIrreducibleRepresentation := True` predicate to become strong
globally, a branch-spectrum cell carries tensor-irreducible SU(7) atoms
directly.  The cell still stores no `Nat.Prime`, no `PrimeExponent`, and no
Goldbach pair.  Prime edges are computed from the tensor-irreducibility proofs
at projection time.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-- Tensor-irreducible atoms have prime raw atom codes. -/
theorem tensorIrreducibleAtom_atomCode_prime
    {C : SU7WeightTensorCoding}
    (a : SU7TensorIrreducibleAtom C) :
    Nat.Prime (atomCode a.toSU7Atom) := by
  simpa using primeCode_of_tensorIrreducible C a.tensor_irreducible

/-! ## Tensor-irreducible branch-spectrum cells -/

/-- A branch-spectrum cell whose left/right atoms are tensor-irreducible.

No prime fields are stored in this object. -/
structure SU7TensorIrreducibleBranchingSpectrumCell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftAtom : SU7TensorIrreducibleAtom C
  rightAtom : SU7TensorIrreducibleAtom C

/-- Forget a tensor-irreducible branch cell to the existing physical spectrum
cell shape. -/
def physicalBranchingSpectrumCell_of_tensorIrreducibleCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    SU7PhysicalBranchingSpectrumCell n where
  branch := B.branch
  leftAtom := B.leftAtom.toSU7Atom
  rightAtom := B.rightAtom.toSU7Atom
  colorLoop :=
    { fiber := n
      leftAtom := B.leftAtom.toSU7Atom
      rightAtom := B.rightAtom.toSU7Atom }
  allowed := by trivial
  loop_fiber := rfl
  loop_left := rfl
  loop_right := rfl

/-- Raw residual of a tensor-irreducible branch-spectrum cell. -/
def tensorIrreducibleBranchingSpectrumResidual
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) : ℤ :=
  rawAtomCodePhysicalBranchingSpectrumResidual
    (physicalBranchingSpectrumCell_of_tensorIrreducibleCell B)

/-- Zero tensor-irreducible raw residual is exactly even-fiber balance under
the tensor atoms' raw codes. -/
theorem tensorIrreducibleBranchingSpectrumResidual_zero_to_sum
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hzero : tensorIrreducibleBranchingSpectrumResidual B = 0) :
    atomCode B.leftAtom.toSU7Atom +
      atomCode B.rightAtom.toSU7Atom = 2 * n := by
  exact rawAtomCodePhysicalBranchingSpectrumResidual_zero_to_sum
    (physicalBranchingSpectrumCell_of_tensorIrreducibleCell B) hzero

/-! ## Direct prime-edge projection from tensor-irreducible cells -/

/-- Prime-edge projection computed from the tensor-irreducibility proofs.

This projection uses neither stored primes nor the `Nat.nth Nat.Prime`
readout. -/
def primeEdgeBranchCell_of_tensorIrreducibleCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    SU7PrimeEdgeBranchCell n where
  branch := B.branch
  leftPrime :=
    ⟨atomCode B.leftAtom.toSU7Atom,
      tensorIrreducibleAtom_atomCode_prime B.leftAtom⟩
  rightPrime :=
    ⟨atomCode B.rightAtom.toSU7Atom,
      tensorIrreducibleAtom_atomCode_prime B.rightAtom⟩

@[simp] theorem primeEdgeBranchCell_of_tensorIrreducibleCell_left
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    (primeEdgeBranchCell_of_tensorIrreducibleCell B).leftPrime.1 =
      atomCode B.leftAtom.toSU7Atom := rfl

@[simp] theorem primeEdgeBranchCell_of_tensorIrreducibleCell_right
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    (primeEdgeBranchCell_of_tensorIrreducibleCell B).rightPrime.1 =
      atomCode B.rightAtom.toSU7Atom := rfl

/-- Tensor-irreducible prime-edge projection preserves the raw cell residual.
-/
theorem branchWeightResidual_tensorIrreducibleProjection_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    branchWeightResidual (primeEdgeBranchCell_of_tensorIrreducibleCell B) =
      tensorIrreducibleBranchingSpectrumResidual B := by
  rfl

/-- Zero residual makes the tensor-irreducible projection trace-neutral. -/
theorem traceNeutral_of_tensorIrreducibleResidual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hzero : tensorIrreducibleBranchingSpectrumResidual B = 0) :
    (primeEdgeBranchCell_of_tensorIrreducibleCell B).traceNeutral := by
  exact
    (branchWeightResidual_eq_zero_iff_traceNeutral
      (primeEdgeBranchCell_of_tensorIrreducibleCell B)).mp
      (by simpa [branchWeightResidual_tensorIrreducibleProjection_eq B]
        using hzero)

/-- A tensor-irreducible residual-zero branch cell computes a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_tensorIrreducibleCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hzero : tensorIrreducibleBranchingSpectrumResidual B = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (primeEdgeBranchCell_of_tensorIrreducibleCell B)
    (traceNeutral_of_tensorIrreducibleResidual_zero B hzero)

/-! ## Certificate -/

/-- P906 certificate: tensor-irreducible branch-spectrum cells generate
prime-edge loops locally, without a global placeholder-irreducibility
realization law. -/
structure SU7TensorIrreducibleCellProjectionCertificate where
  tensor_atom_to_physical :
    ∀ {C : SU7WeightTensorCoding},
      SU7TensorIrreducibleAtom C -> SU7Atom
  tensor_atom_code_prime :
    ∀ {C : SU7WeightTensorCoding}
      (a : SU7TensorIrreducibleAtom C),
      Nat.Prime (atomCode a.toSU7Atom)
  tensor_cell_to_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7TensorIrreducibleBranchingSpectrumCell C n ->
        SU7PhysicalBranchingSpectrumCell n
  tensor_cell_zero_to_sum :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7TensorIrreducibleBranchingSpectrumCell C n),
      tensorIrreducibleBranchingSpectrumResidual B = 0 ->
        atomCode B.leftAtom.toSU7Atom +
          atomCode B.rightAtom.toSU7Atom = 2 * n
  tensor_cell_to_prime_edge :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7TensorIrreducibleBranchingSpectrumCell C n ->
        SU7PrimeEdgeBranchCell n
  tensor_projection_preserves_residual :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7TensorIrreducibleBranchingSpectrumCell C n),
      branchWeightResidual (primeEdgeBranchCell_of_tensorIrreducibleCell B) =
        tensorIrreducibleBranchingSpectrumResidual B
  tensor_cell_zero_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7TensorIrreducibleBranchingSpectrumCell C n),
      tensorIrreducibleBranchingSpectrumResidual B = 0 ->
        TraceZeroPrimeEdgeLoop n

def su7TensorIrreducibleCellProjectionCertificate :
    SU7TensorIrreducibleCellProjectionCertificate where
  tensor_atom_to_physical := SU7TensorIrreducibleAtom.toSU7Atom
  tensor_atom_code_prime := tensorIrreducibleAtom_atomCode_prime
  tensor_cell_to_physical :=
    physicalBranchingSpectrumCell_of_tensorIrreducibleCell
  tensor_cell_zero_to_sum :=
    tensorIrreducibleBranchingSpectrumResidual_zero_to_sum
  tensor_cell_to_prime_edge :=
    primeEdgeBranchCell_of_tensorIrreducibleCell
  tensor_projection_preserves_residual :=
    branchWeightResidual_tensorIrreducibleProjection_eq
  tensor_cell_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_tensorIrreducibleCell


end
end StandardModelConstraint
end SaturationMonoid
