import H0mework.Arithmetic.ShellSources.P922

/-!
# Proposition 923: raw-code tensor irreducibility is multiplicative atomicity

P922 made certified raw cell lists the concrete generator target.  This file
lowers the endpoint certificate one more step for the canonical raw-code
tensor carrier:

```text
SU7TensorIrreducible rawCodeTensorCoding { code := k }
  <-> NatMultiplicativelyAtomic k
```

The producer object below stores atomicity proofs, not `Nat.Prime` proofs.
Primality remains a downstream projection through P904/P905.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Raw-code tensor normal form -/

/-- Multiplicative atomicity of a raw code gives tensor irreducibility for the
canonical raw-code tensor carrier. -/
theorem rawCodeTensorIrreducible_of_atomic
    {w : SU7WeightLattice}
    (h : NatMultiplicativelyAtomic w.code) :
    SU7TensorIrreducible rawCodeTensorCoding w := by
  constructor
  · exact h.1
  · intro u v htensor
    have hfactor : w.code = u.code * v.code := by
      simpa [rawCodeTensorCoding] using htensor.symm
    exact h.2 u.code v.code hfactor

/-- For the canonical raw-code tensor carrier, tensor irreducibility is exactly
multiplicative atomicity of the raw code. -/
theorem rawCodeTensorIrreducible_iff_atomic
    (w : SU7WeightLattice) :
    SU7TensorIrreducible rawCodeTensorCoding w ↔
      NatMultiplicativelyAtomic w.code := by
  constructor
  · intro h
    exact natMultiplicativelyAtomic_of_tensorIrreducible
      rawCodeTensorCoding h
  · exact rawCodeTensorIrreducible_of_atomic

/-- The same normal form may be read as primality, but this theorem is a
projection statement, not the producer object used below. -/
theorem rawCodeTensorIrreducible_iff_prime
    (w : SU7WeightLattice) :
    SU7TensorIrreducible rawCodeTensorCoding w ↔
      Nat.Prime w.code := by
  rw [rawCodeTensorIrreducible_iff_atomic,
    natMultiplicativelyAtomic_iff_prime]

/-! ## Atomic raw cell lists -/

/-- A raw branching cell whose endpoint codes are multiplicatively atomic.

This object stores no `Nat.Prime` proof. -/
structure SU7AtomicRawBranchingCell (n : ℕ) where
  cell : SU7BranchingDecompositionCell n
  left_atomic : NatMultiplicativelyAtomic cell.leftWeightCode
  right_atomic : NatMultiplicativelyAtomic cell.rightWeightCode

/-- An atomic raw branching cell generates a P922 certified raw branching cell
for the canonical raw-code tensor carrier. -/
def certifiedRawBranchingCell_of_atomicRawBranchingCell
    {n : ℕ} (x : SU7AtomicRawBranchingCell n) :
    SU7CertifiedRawBranchingCell rawCodeTensorCoding n where
  cell := x.cell
  left_tensor_irreducible :=
    rawCodeTensorIrreducible_of_atomic x.left_atomic
  right_tensor_irreducible :=
    rawCodeTensorIrreducible_of_atomic x.right_atomic

/-- Forget an atomic raw cell list to P922's certified raw cell list. -/
def certifiedRawBranchingCells_of_atomicRawBranchingCells
    {n : ℕ} (xs : List (SU7AtomicRawBranchingCell n)) :
    List (SU7CertifiedRawBranchingCell rawCodeTensorCoding n) :=
  xs.map certifiedRawBranchingCell_of_atomicRawBranchingCell

/-- Membership in the certified list generated from atomic cells comes from an
atomic source cell. -/
theorem exists_atomicCell_of_mem_certifiedAtomicList
    {n : ℕ} (xs : List (SU7AtomicRawBranchingCell n))
    {c : SU7CertifiedRawBranchingCell rawCodeTensorCoding n}
    (hmem :
      c ∈ certifiedRawBranchingCells_of_atomicRawBranchingCells xs) :
    ∃ x : SU7AtomicRawBranchingCell n,
      x ∈ xs ∧
        certifiedRawBranchingCell_of_atomicRawBranchingCell x = c := by
  unfold certifiedRawBranchingCells_of_atomicRawBranchingCells at hmem
  exact List.mem_map.mp hmem

/-! ## Checked atomic lists -/

/-- A checked atomic raw branching list.  It is P922's checked list with
endpoint certificates lowered from tensor irreducibility to multiplicative
atomicity. -/
structure SU7AtomicRawBranchingCheckedCellList (n : ℕ) where
  cells : List (SU7AtomicRawBranchingCell n)
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈
      (rawBranchingSpectrum_of_certifiedCells
        (certifiedRawBranchingCells_of_atomicRawBranchingCells cells)).cells
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈
        (rawBranchingSpectrum_of_certifiedCells
          (certifiedRawBranchingCells_of_atomicRawBranchingCells cells)).cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  coverage_check :
    rawBranchingEnergyShellCoverageCheck
      (rawBranchingSpectrum_of_certifiedCells
        (certifiedRawBranchingCells_of_atomicRawBranchingCells cells))
      maxEnergy = true

/-- A checked atomic raw list generates P922's checked certified list. -/
def certifiedCellList_of_atomicCheckedCellList
    {n : ℕ} (L : SU7AtomicRawBranchingCheckedCellList n) :
    SU7CertifiedRawBranchingCheckedCellList rawCodeTensorCoding n where
  cells := certifiedRawBranchingCells_of_atomicRawBranchingCells L.cells
  startCell := L.startCell
  start_mem := L.start_mem
  maxEnergy := L.maxEnergy
  energy_bound := L.energy_bound
  coverage_check := L.coverage_check

/-- A checked atomic raw list computes a generated physical zero branch cell.
-/
def generatedPhysicalZeroBranchCell_of_atomicCheckedCellList
    {n : ℕ} (L : SU7AtomicRawBranchingCheckedCellList n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_certifiedCellList
    (certifiedCellList_of_atomicCheckedCellList L)

/-- A checked atomic raw list computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_atomicCheckedCellList
    {n : ℕ} (L : SU7AtomicRawBranchingCheckedCellList n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_atomicCheckedCellList L)

/-- Every even fiber carries a checked atomic raw branching list. -/
def SU7AtomicRawBranchingCheckedCellListEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7AtomicRawBranchingCheckedCellList n)

/-- Fiberwise checked atomic raw lists generate P922 certified checked lists.
-/
def certifiedCellListsEveryEvenFiber_of_atomicCheckedCellLists
    (H : SU7AtomicRawBranchingCheckedCellListEveryEvenFiber) :
    SU7CertifiedRawBranchingCheckedCellListEveryEvenFiber
      rawCodeTensorCoding := by
  intro n hn
  exact ⟨certifiedCellList_of_atomicCheckedCellList
    (Classical.choice (H n hn))⟩

/-- Fiberwise checked atomic raw lists give ordinary even Goldbach through
P923 -> P922 -> P921. -/
theorem evenGoldbach_of_atomicCheckedCellLists
    (H : SU7AtomicRawBranchingCheckedCellListEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_certifiedCellLists
    (certifiedCellListsEveryEvenFiber_of_atomicCheckedCellLists H)

/-! ## Certificate -/

/-- P923 certificate: raw-code tensor irreducibility is multiplicative
atomicity, and atomic raw checked lists feed the P922 producer. -/
structure SU7RawCodeAtomicListProducerCertificate where
  raw_tensor_irreducible_iff_atomic :
    ∀ w : SU7WeightLattice,
      SU7TensorIrreducible rawCodeTensorCoding w ↔
        NatMultiplicativelyAtomic w.code
  raw_tensor_irreducible_iff_prime :
    ∀ w : SU7WeightLattice,
      SU7TensorIrreducible rawCodeTensorCoding w ↔
        Nat.Prime w.code
  atomic_cell_to_certified :
    ∀ {n : ℕ}, SU7AtomicRawBranchingCell n ->
      SU7CertifiedRawBranchingCell rawCodeTensorCoding n
  atomic_checked_to_certified_checked :
    ∀ {n : ℕ}, SU7AtomicRawBranchingCheckedCellList n ->
      SU7CertifiedRawBranchingCheckedCellList rawCodeTensorCoding n
  every_fiber_to_goldbach :
    SU7AtomicRawBranchingCheckedCellListEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P923 atomic-list producer certificate. -/
def su7RawCodeAtomicListProducerCertificate :
    SU7RawCodeAtomicListProducerCertificate where
  raw_tensor_irreducible_iff_atomic :=
    rawCodeTensorIrreducible_iff_atomic
  raw_tensor_irreducible_iff_prime :=
    rawCodeTensorIrreducible_iff_prime
  atomic_cell_to_certified :=
    certifiedRawBranchingCell_of_atomicRawBranchingCell
  atomic_checked_to_certified_checked :=
    certifiedCellList_of_atomicCheckedCellList
  every_fiber_to_goldbach :=
    evenGoldbach_of_atomicCheckedCellLists


end
end StandardModelConstraint
end SaturationMonoid
