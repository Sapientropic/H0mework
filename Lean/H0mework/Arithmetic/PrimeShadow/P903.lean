import H0mework.Arithmetic.ShellSources.P902

/-!
# Proposition 903: raw SU(7) atom-code projection to prime edges

P879/P892 provide a canonical prime-coded readout by sending every raw weight
index to `Nat.nth Nat.Prime`.  That is useful as a faithful readout layer, but
it makes primality a property of the readout function itself.

This file fixes the sharper producer boundary.  The projection below uses the
raw `atomCode` carried by the SU(7) atom.  It produces prime-edge data only
from the genuine representation-theoretic throat isolated in P878:

```text
SU7IrreducibleCodePrimeProducerLaw
```

Thus the cells still store no `Nat.Prime`, no `PrimeExponent`, and no Goldbach
pair.  Prime edges are outputs of a raw atom-code projection theorem, not
stored data and not `Nat.nth` enumeration.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Raw atom-code residual on physical branch-spectrum cells -/

/-- Raw atom-code residual of a physical branch-spectrum cell.

Unlike `physicalBranchingSpectrumResidual`, this uses `atomCode` directly and
does not pass through the canonical `Nat.nth Nat.Prime` readout. -/
def rawAtomCodePhysicalBranchingSpectrumResidual
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) : ℤ :=
  ((atomCode C.leftAtom + atomCode C.rightAtom : ℕ) : ℤ) -
    ((2 * n : ℕ) : ℤ)

/-- Zero raw residual is exactly even-fiber balance under raw atom codes. -/
theorem rawAtomCodePhysicalBranchingSpectrumResidual_zero_to_sum
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : rawAtomCodePhysicalBranchingSpectrumResidual C = 0) :
    atomCode C.leftAtom + atomCode C.rightAtom = 2 * n := by
  unfold rawAtomCodePhysicalBranchingSpectrumResidual at hzero
  omega

/-! ## Projection from non-storing physical cells using the real throat -/

/-- Raw-code prime-edge projection of a physical branch-spectrum cell.

The input cell stores only SU(7) atoms and gauge data.  The output prime proofs
come from `SU7IrreducibleCodePrimeProducerLaw`, applied to the atoms'
irreducibility proofs. -/
def rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    SU7PrimeEdgeBranchCell n where
  branch := C.branch
  leftPrime := ⟨atomCode C.leftAtom,
    H C.leftAtom.weight C.leftAtom.irreducible⟩
  rightPrime := ⟨atomCode C.rightAtom,
    H C.rightAtom.weight C.rightAtom.irreducible⟩

@[simp] theorem rawPrimeEdgeBranchCell_of_physical_left
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).leftPrime.1 =
      atomCode C.leftAtom := rfl

@[simp] theorem rawPrimeEdgeBranchCell_of_physical_right
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).rightPrime.1 =
      atomCode C.rightAtom := rfl

/-- The raw-code projection produces a prime left edge. -/
theorem rawPhysicalBranchingSpectrumCell_leftPrime_generated
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    Nat.Prime
      (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).leftPrime.1 :=
  (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).leftPrime.2

/-- The raw-code projection produces a prime right edge. -/
theorem rawPhysicalBranchingSpectrumCell_rightPrime_generated
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    Nat.Prime
      (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).rightPrime.1 :=
  (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).rightPrime.2

/-- Raw-code prime-edge projection preserves the raw residual. -/
theorem branchWeightResidual_rawPhysicalProjection_eq
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    branchWeightResidual
        (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C) =
      rawAtomCodePhysicalBranchingSpectrumResidual C := by
  rfl

/-- Zero raw physical residual makes the raw projected prime-edge cell
trace-neutral. -/
theorem traceNeutral_of_rawPhysicalBranchingSpectrumResidual_zero
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : rawAtomCodePhysicalBranchingSpectrumResidual C = 0) :
    (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C).traceNeutral := by
  exact
    (branchWeightResidual_eq_zero_iff_traceNeutral
      (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C)).mp
      (by simpa [branchWeightResidual_rawPhysicalProjection_eq H C] using hzero)

/-- Zero raw physical residual computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : rawAtomCodePhysicalBranchingSpectrumResidual C = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C)
    (traceNeutral_of_rawPhysicalBranchingSpectrumResidual_zero H C hzero)

/-! ## Raw-code residual on branching-decomposition cells -/

/-- Raw atom-code residual of a branching-decomposition cell. -/
def rawAtomCodeBranchingDecompositionResidual
    {n : ℕ} (C : SU7BranchingDecompositionCell n) : ℤ :=
  rawAtomCodePhysicalBranchingSpectrumResidual
    (physicalBranchingSpectrumCell_of_branchingDecompositionCell C)

/-- Zero raw decomposition residual is exactly even-fiber balance under the
generated raw SU(7) atoms. -/
theorem rawAtomCodeBranchingDecompositionResidual_zero_to_sum
    {n : ℕ} (C : SU7BranchingDecompositionCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual C = 0) :
    atomCode (leftAtomOfBranchingDecompositionCell C) +
      atomCode (rightAtomOfBranchingDecompositionCell C) = 2 * n := by
  exact rawAtomCodePhysicalBranchingSpectrumResidual_zero_to_sum
    (physicalBranchingSpectrumCell_of_branchingDecompositionCell C) hzero

/-- Raw-code prime-edge projection of a branching-decomposition cell. -/
def rawPrimeEdgeBranchCell_of_branchingDecompositionCell
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n) :
    SU7PrimeEdgeBranchCell n :=
  rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H
    (physicalBranchingSpectrumCell_of_branchingDecompositionCell C)

/-- Raw-code branching-decomposition projection preserves raw residual. -/
theorem branchWeightResidual_rawBranchingDecompositionProjection_eq
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n) :
    branchWeightResidual
        (rawPrimeEdgeBranchCell_of_branchingDecompositionCell H C) =
      rawAtomCodeBranchingDecompositionResidual C := by
  rfl

/-- Zero raw branching-decomposition residual computes a trace-zero prime-edge
loop. -/
def traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual
    (H : SU7IrreducibleCodePrimeProducerLaw)
    {n : ℕ} (C : SU7BranchingDecompositionCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual C = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    (rawPrimeEdgeBranchCell_of_branchingDecompositionCell H C)
    ((branchWeightResidual_eq_zero_iff_traceNeutral
      (rawPrimeEdgeBranchCell_of_branchingDecompositionCell H C)).mp
      (by simpa [branchWeightResidual_rawBranchingDecompositionProjection_eq H C]
        using hzero))

/-! ## Certificate -/

/-- P903 certificate: non-storing SU(7) cells project to prime edges through
the raw irreducible-code producer throat, not through stored primes and not
through `Nat.nth Nat.Prime`. -/
structure SU7RawAtomCodeBranchProjectionCertificate where
  raw_physical_residual_zero_to_sum :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      rawAtomCodePhysicalBranchingSpectrumResidual C = 0 ->
        atomCode C.leftAtom + atomCode C.rightAtom = 2 * n
  project_physical_cell :
    SU7IrreducibleCodePrimeProducerLaw ->
      ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumCell n ->
        SU7PrimeEdgeBranchCell n
  physical_projection_preserves_raw_residual :
    ∀ (H : SU7IrreducibleCodePrimeProducerLaw)
      {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      branchWeightResidual
          (rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell H C) =
        rawAtomCodePhysicalBranchingSpectrumResidual C
  raw_physical_residual_zero_to_trace_zero :
    ∀ (_H : SU7IrreducibleCodePrimeProducerLaw)
      {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      rawAtomCodePhysicalBranchingSpectrumResidual C = 0 ->
        TraceZeroPrimeEdgeLoop n
  raw_decomposition_residual_zero_to_sum :
    ∀ {n : ℕ} (C : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidual C = 0 ->
        atomCode (leftAtomOfBranchingDecompositionCell C) +
          atomCode (rightAtomOfBranchingDecompositionCell C) = 2 * n
  project_decomposition_cell :
    SU7IrreducibleCodePrimeProducerLaw ->
      ∀ {n : ℕ}, SU7BranchingDecompositionCell n ->
        SU7PrimeEdgeBranchCell n
  raw_decomposition_residual_zero_to_trace_zero :
    ∀ (_H : SU7IrreducibleCodePrimeProducerLaw)
      {n : ℕ} (C : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidual C = 0 ->
        TraceZeroPrimeEdgeLoop n
  raw_irreducible_throat_iff_atom_projection :
    SU7IrreducibleCodePrimeProducerLaw ↔ SU7AtomCodePrimeProjectionLaw

def su7RawAtomCodeBranchProjectionCertificate :
    SU7RawAtomCodeBranchProjectionCertificate where
  raw_physical_residual_zero_to_sum :=
    rawAtomCodePhysicalBranchingSpectrumResidual_zero_to_sum
  project_physical_cell :=
    rawPrimeEdgeBranchCell_of_physicalBranchingSpectrumCell
  physical_projection_preserves_raw_residual :=
    branchWeightResidual_rawPhysicalProjection_eq
  raw_physical_residual_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual
  raw_decomposition_residual_zero_to_sum :=
    rawAtomCodeBranchingDecompositionResidual_zero_to_sum
  project_decomposition_cell :=
    rawPrimeEdgeBranchCell_of_branchingDecompositionCell
  raw_decomposition_residual_zero_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual
  raw_irreducible_throat_iff_atom_projection :=
    SU7IrreducibleCodePrimeProducerLaw_iff_atomCodeProjection


end
end StandardModelConstraint
end SaturationMonoid
