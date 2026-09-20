import H0mework.Arithmetic.CodePairs.P923

/-!
# Proposition 924: non-prime-storing SU(7) branch cells project to prime edges

P923 lowered the executable branch producer to checked raw cells whose endpoint
certificates are `NatMultiplicativelyAtomic`, not `Nat.Prime`.

This file makes the projection boundary explicit at the single-cell level.  A
`SU7AtomicPhysicalBranchCell` stores a physical branch cell plus atomic endpoint
certificates.  It stores no prime edge and no Goldbach pair.  Lean then proves
that its atom-code projection computes a `SU7PrimeEdgeBranchCell`; if the
physical residual is zero, the projection lands in the trace-zero fiber.

This is the local shape requested by the producer spine:

```text
raw SU(7) branching cell + atomic endpoint certificates
  -> non-prime physical branch cell
  -> prime-edge projection theorem
```
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Physical cells with atomic endpoint certificates -/

/-- A physical SU(7) branch cell whose two endpoint atom codes are
multiplicatively atomic.

This object deliberately stores no `Nat.Prime`, no `PrimeExponent`, and no
trace-zero loop. -/
structure SU7AtomicPhysicalBranchCell (n : ℕ) where
  cell : SU7PhysicalBranchCell n
  left_atomic : NatMultiplicativelyAtomic (atomCode cell.leftAtom)
  right_atomic : NatMultiplicativelyAtomic (atomCode cell.rightAtom)

/-- The left endpoint of an atomic physical branch cell projects to a prime
only at the readout boundary. -/
theorem atomicPhysicalBranchCell_left_atomCode_prime
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    Nat.Prime (atomCode B.cell.leftAtom) :=
  Nat.Prime.of_multiplicativelyAtomic B.left_atomic

/-- The right endpoint of an atomic physical branch cell projects to a prime
only at the readout boundary. -/
theorem atomicPhysicalBranchCell_right_atomCode_prime
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    Nat.Prime (atomCode B.cell.rightAtom) :=
  Nat.Prime.of_multiplicativelyAtomic B.right_atomic

/-- Prime-edge projection computed from endpoint atomicity. -/
def primeEdgeBranchCell_of_atomicPhysicalBranchCell
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    SU7PrimeEdgeBranchCell n where
  branch := SU3FlagSchubertCell.e
  leftPrime :=
    ⟨atomCode B.cell.leftAtom,
      atomicPhysicalBranchCell_left_atomCode_prime B⟩
  rightPrime :=
    ⟨atomCode B.cell.rightAtom,
      atomicPhysicalBranchCell_right_atomCode_prime B⟩

@[simp] theorem primeEdgeBranchCell_of_atomicPhysical_left
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    (primeEdgeBranchCell_of_atomicPhysicalBranchCell B).leftPrime.1 =
      atomCode B.cell.leftAtom := rfl

@[simp] theorem primeEdgeBranchCell_of_atomicPhysical_right
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    (primeEdgeBranchCell_of_atomicPhysicalBranchCell B).rightPrime.1 =
      atomCode B.cell.rightAtom := rfl

/-- Atomic physical projection preserves the P873 physical residual. -/
theorem branchWeightResidual_atomicPhysicalProjection_eq
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n) :
    branchWeightResidual
        (primeEdgeBranchCell_of_atomicPhysicalBranchCell B) =
      physicalResidual B.cell := by
  rfl

/-- Zero physical residual makes the atomic physical projection trace-neutral.
-/
theorem traceNeutral_of_atomicPhysicalResidual_zero
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n)
    (hzero : physicalResidual B.cell = 0) :
    (primeEdgeBranchCell_of_atomicPhysicalBranchCell B).traceNeutral := by
  exact
    (branchWeightResidual_eq_zero_iff_traceNeutral
      (primeEdgeBranchCell_of_atomicPhysicalBranchCell B)).mp
      (by
        simpa [branchWeightResidual_atomicPhysicalProjection_eq B] using hzero)

/-- A zero-residual atomic physical branch cell computes a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_atomicPhysicalBranchCell
    {n : ℕ} (B : SU7AtomicPhysicalBranchCell n)
    (hzero : physicalResidual B.cell = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (primeEdgeBranchCell_of_atomicPhysicalBranchCell B)
    (traceNeutral_of_atomicPhysicalResidual_zero B hzero)

/-! ## Raw atomic branching cells to physical branch cells -/

/-- Tensor-irreducible branch cell generated from one P923 raw atomic cell.

The construction uses multiplicative atomicity to build tensor irreducibility
for the canonical raw-code tensor carrier; it does not build or store prime
edges. -/
def tensorIrreducibleCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    SU7TensorIrreducibleBranchingSpectrumCell rawCodeTensorCoding n where
  branch := x.cell.branch
  leftAtom :=
    { weight := { code := x.cell.leftWeightCode }
      tensor_irreducible :=
        rawCodeTensorIrreducible_of_atomic x.left_atomic
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints x.cell.incidence).1 }
  rightAtom :=
    { weight := { code := x.cell.rightWeightCode }
      tensor_irreducible :=
        rawCodeTensorIrreducible_of_atomic x.right_atomic
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints x.cell.incidence).2 }

/-- The tensor lift of an atomic raw cell preserves raw residual exactly. -/
theorem tensorIrreducibleCell_of_atomicRawBranchingCell_rawResidual_eq
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    tensorIrreducibleBranchingSpectrumResidual
        (tensorIrreducibleCell_of_atomicRawBranchingCell x) =
      rawAtomCodeBranchingDecompositionResidual x.cell := by
  rfl

/-- Forget one P923 raw atomic cell to a P873 physical branch cell. -/
def physicalBranchCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    SU7PhysicalBranchCell n :=
  physicalBranchCell_of_tensorIrreducibleCell
    (tensorIrreducibleCell_of_atomicRawBranchingCell x)

/-- The physical residual of the generated physical cell is exactly the raw
branching-decomposition residual. -/
theorem physicalResidual_atomicRawBranchingCell_eq
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    physicalResidual (physicalBranchCell_of_atomicRawBranchingCell x) =
      rawAtomCodeBranchingDecompositionResidual x.cell := by
  rfl

/-- A raw atomic branching cell generates an atomic physical branch cell. -/
def atomicPhysicalBranchCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    SU7AtomicPhysicalBranchCell n where
  cell := physicalBranchCell_of_atomicRawBranchingCell x
  left_atomic := by
    simpa [physicalBranchCell_of_atomicRawBranchingCell,
      physicalBranchCell_of_tensorIrreducibleCell,
      physicalBranchCell_of_physicalSpectrumCell,
      physicalBranchingSpectrumCell_of_tensorIrreducibleCell,
      tensorIrreducibleCell_of_atomicRawBranchingCell] using x.left_atomic
  right_atomic := by
    simpa [physicalBranchCell_of_atomicRawBranchingCell,
      physicalBranchCell_of_tensorIrreducibleCell,
      physicalBranchCell_of_physicalSpectrumCell,
      physicalBranchingSpectrumCell_of_tensorIrreducibleCell,
      tensorIrreducibleCell_of_atomicRawBranchingCell] using x.right_atomic

/-- The prime-edge projection of a raw atomic cell is computed only after the
non-prime physical branch cell is generated. -/
def primeEdgeBranchCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    SU7PrimeEdgeBranchCell n :=
  primeEdgeBranchCell_of_atomicPhysicalBranchCell
    (atomicPhysicalBranchCell_of_atomicRawBranchingCell x)

/-- The raw atomic projection preserves the raw branching residual. -/
theorem branchWeightResidual_atomicRawProjection_eq
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    branchWeightResidual (primeEdgeBranchCell_of_atomicRawBranchingCell x) =
      rawAtomCodeBranchingDecompositionResidual x.cell := by
  rfl

/-- Zero raw residual computes a trace-zero prime-edge loop from a raw atomic
cell, with primality appearing only as the projection theorem. -/
def traceZeroPrimeEdgeLoop_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual x.cell = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_atomicPhysicalBranchCell
    (atomicPhysicalBranchCell_of_atomicRawBranchingCell x)
    (by
      change physicalResidual (physicalBranchCell_of_atomicRawBranchingCell x) =
        0
      simpa [physicalResidual_atomicRawBranchingCell_eq x] using hzero)

/-- Zero raw residual produces the P909 generated physical zero-cell package.
-/
def generatedPhysicalZeroBranchCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual x.cell = 0) :
    SU7GeneratedPhysicalZeroBranchCell n where
  cell := physicalBranchCell_of_atomicRawBranchingCell x
  residual_zero := by
    simpa [physicalResidual_atomicRawBranchingCell_eq x] using hzero
  left_atomCode_prime :=
    atomicPhysicalBranchCell_left_atomCode_prime
      (atomicPhysicalBranchCell_of_atomicRawBranchingCell x)
  right_atomCode_prime :=
    atomicPhysicalBranchCell_right_atomCode_prime
      (atomicPhysicalBranchCell_of_atomicRawBranchingCell x)

/-- The generated physical zero package and the direct atomic projection give
the same trace-zero prime-edge loop. -/
theorem traceZeroPrimeEdgeLoop_atomicRaw_eq_generatedPhysical
    {n : ℕ} (x : SU7AtomicRawBranchingCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual x.cell = 0) :
    traceZeroPrimeEdgeLoop_of_atomicRawBranchingCell x hzero =
      traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
        (generatedPhysicalZeroBranchCell_of_atomicRawBranchingCell x hzero) := by
  rfl

/-! ## Certificate -/

/-- P924 certificate: non-prime SU(7) branch cells generate prime-edge
readouts only at projection time. -/
structure SU7NonPrimeBranchCellProjectionCertificate where
  atomic_physical_to_prime_edge :
    ∀ {n : ℕ}, SU7AtomicPhysicalBranchCell n -> SU7PrimeEdgeBranchCell n
  atomic_physical_residual_preserved :
    ∀ {n : ℕ} (B : SU7AtomicPhysicalBranchCell n),
      branchWeightResidual
          (primeEdgeBranchCell_of_atomicPhysicalBranchCell B) =
        physicalResidual B.cell
  atomic_physical_zero_to_trace_zero :
    ∀ {n : ℕ} (B : SU7AtomicPhysicalBranchCell n),
      physicalResidual B.cell = 0 -> TraceZeroPrimeEdgeLoop n
  atomic_raw_to_physical :
    ∀ {n : ℕ}, SU7AtomicRawBranchingCell n ->
      SU7AtomicPhysicalBranchCell n
  atomic_raw_residual_preserved :
    ∀ {n : ℕ} (x : SU7AtomicRawBranchingCell n),
      branchWeightResidual
          (primeEdgeBranchCell_of_atomicRawBranchingCell x) =
        rawAtomCodeBranchingDecompositionResidual x.cell
  atomic_raw_zero_to_generated_physical :
    ∀ {n : ℕ} (x : SU7AtomicRawBranchingCell n),
      rawAtomCodeBranchingDecompositionResidual x.cell = 0 ->
        SU7GeneratedPhysicalZeroBranchCell n
  atomic_raw_zero_to_trace_zero :
    ∀ {n : ℕ} (x : SU7AtomicRawBranchingCell n),
      rawAtomCodeBranchingDecompositionResidual x.cell = 0 ->
        TraceZeroPrimeEdgeLoop n

/-- Canonical P924 projection certificate. -/
def su7NonPrimeBranchCellProjectionCertificate :
    SU7NonPrimeBranchCellProjectionCertificate where
  atomic_physical_to_prime_edge :=
    primeEdgeBranchCell_of_atomicPhysicalBranchCell
  atomic_physical_residual_preserved :=
    branchWeightResidual_atomicPhysicalProjection_eq
  atomic_physical_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_atomicPhysicalBranchCell
  atomic_raw_to_physical :=
    atomicPhysicalBranchCell_of_atomicRawBranchingCell
  atomic_raw_residual_preserved :=
    branchWeightResidual_atomicRawProjection_eq
  atomic_raw_zero_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_atomicRawBranchingCell
  atomic_raw_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_atomicRawBranchingCell


end
end StandardModelConstraint
end SaturationMonoid
