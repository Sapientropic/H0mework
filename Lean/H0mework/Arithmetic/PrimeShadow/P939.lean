import H0mework.Arithmetic.ShellSources.P932
import H0mework.Physics.BranchSources.P921

/-!
# Proposition 939: branch-rule spectrum cells generate prime edges

P932 already defines a no-prime SU(7) branching-spectrum cell: it stores
tensor-irreducible endpoint atoms, and primality appears only after projection.

This file lowers the source object one more step.  A branch-rule spectrum cell
stores only:

* one raw `SU7BranchingDecompositionCell`;
* membership in a finite raw branch spectrum.

It stores no `Nat.Prime`, no `PrimeExponent`, no trace-zero loop, and no
endpoint irreducibility proof.  A local branch-rule tensor filter supplies
irreducibility only for cells in the spectrum.  From that, Lean constructs the
P932 no-prime cell and then proves that the prime-edge readout is generated at
projection time.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Raw branch-rule spectrum cells -/

/-- A raw branch-rule spectrum cell.

The object carries only the raw SU(7) branching-decomposition data and a proof
that this cell belongs to the branch spectrum under discussion.  It deliberately
contains no prime proof and no tensor-irreducibility proof. -/
structure SU7BranchRuleSpectrumCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) where
  rawCell : SU7BranchingDecompositionCell n
  raw_mem : rawCell ∈ S.cells

/-- The left raw code carried by a branch-rule spectrum cell. -/
def SU7BranchRuleSpectrumCell.leftCode
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (B : SU7BranchRuleSpectrumCell S) : ℕ :=
  B.rawCell.leftWeightCode

/-- The right raw code carried by a branch-rule spectrum cell. -/
def SU7BranchRuleSpectrumCell.rightCode
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (B : SU7BranchRuleSpectrumCell S) : ℕ :=
  B.rawCell.rightWeightCode

/-- The raw residual of a branch-rule spectrum cell. -/
def branchRuleSpectrumResidual
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (B : SU7BranchRuleSpectrumCell S) : ℤ :=
  rawAtomCodeBranchingDecompositionResidual B.rawCell

/-! ## Projection through a local tensor filter -/

/-- A branch-rule cell becomes a P932 no-prime branch cell once the local
branch rule supplies endpoint tensor irreducibility for in-spectrum cells. -/
def noPrimeBranchingCell_of_branchRuleSpectrumCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    SU7NoPrimeBranchingSpectrumCell C n where
  branch := B.rawCell.branch
  leftAtom :=
    { weight := { code := B.rawCell.leftWeightCode }
      tensor_irreducible :=
        F.left_tensor_irreducible B.rawCell B.raw_mem
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints B.rawCell.incidence).1 }
  rightAtom :=
    { weight := { code := B.rawCell.rightWeightCode }
      tensor_irreducible :=
        F.right_tensor_irreducible B.rawCell B.raw_mem
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints B.rawCell.incidence).2 }

/-- The no-prime projection preserves the raw branch-rule residual. -/
theorem noPrimeBranchingCell_of_branchRuleSpectrumCell_residual_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    noPrimeBranchingResidual
        (noPrimeBranchingCell_of_branchRuleSpectrumCell F B) =
      branchRuleSpectrumResidual B := by
  rfl

/-- The local tensor filter produces primality of the left code at projection
time; the raw cell itself stores no primality proof. -/
theorem branchRuleSpectrumCell_leftCode_prime
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    Nat.Prime B.leftCode := by
  exact
    primeCode_of_tensorIrreducible C
      (F.left_tensor_irreducible B.rawCell B.raw_mem)

/-- The local tensor filter produces primality of the right code at projection
time; the raw cell itself stores no primality proof. -/
theorem branchRuleSpectrumCell_rightCode_prime
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    Nat.Prime B.rightCode := by
  exact
    primeCode_of_tensorIrreducible C
      (F.right_tensor_irreducible B.rawCell B.raw_mem)

/-- Prime-edge projection generated from the branch-rule cell and its local
tensor filter. -/
def primeEdgeBranchCell_of_branchRuleSpectrumCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    SU7PrimeEdgeBranchCell n :=
  primeEdgeBranchCell_of_noPrimeBranchingCell
    (noPrimeBranchingCell_of_branchRuleSpectrumCell F B)

@[simp] theorem primeEdgeBranchCell_of_branchRuleSpectrumCell_left
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    (primeEdgeBranchCell_of_branchRuleSpectrumCell F B).leftPrime.1 =
      B.leftCode := rfl

@[simp] theorem primeEdgeBranchCell_of_branchRuleSpectrumCell_right
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    (primeEdgeBranchCell_of_branchRuleSpectrumCell F B).rightPrime.1 =
      B.rightCode := rfl

/-- The generated prime-edge projection preserves the raw branch-rule
residual. -/
theorem branchWeightResidual_branchRuleProjection_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S) :
    branchWeightResidual
        (primeEdgeBranchCell_of_branchRuleSpectrumCell F B) =
      branchRuleSpectrumResidual B := by
  unfold primeEdgeBranchCell_of_branchRuleSpectrumCell
  rw [branchWeightResidual_noPrimeProjection_eq,
    noPrimeBranchingCell_of_branchRuleSpectrumCell_residual_eq]

/-- Zero raw residual computes the even-fiber arithmetic balance of the raw
codes. -/
theorem branchRuleSpectrumResidual_zero_to_sum
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (B : SU7BranchRuleSpectrumCell S)
    (hzero : branchRuleSpectrumResidual B = 0) :
    B.leftCode + B.rightCode = 2 * n := by
  exact rawAtomCodeBranchingDecompositionResidual_zero_to_sum
    B.rawCell hzero

/-- A zero branch-rule residual computes a trace-zero prime-edge loop only
after the local tensor-filter projection. -/
def traceZeroPrimeEdgeLoop_of_branchRuleSpectrumCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {S : SU7BranchingDecompositionSpectrum n}
    (F : SU7RawBranchingLocalTensorFilter C S)
    (B : SU7BranchRuleSpectrumCell S)
    (hzero : branchRuleSpectrumResidual B = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_noPrimeBranchingCell
    (noPrimeBranchingCell_of_branchRuleSpectrumCell F B)
    (by
      simpa [noPrimeBranchingCell_of_branchRuleSpectrumCell_residual_eq F B]
        using hzero)

/-! ## Certificate -/

/-- P939 certificate: a branch-rule spectrum cell stores only raw branch data;
the local branch rule produces tensor irreducibility, then P932 projects the
result to prime-edge data. -/
structure SU7BranchRuleSpectrumPrimeEdgeProjectionCertificate where
  cell_to_no_prime :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n},
      SU7RawBranchingLocalTensorFilter C S ->
        SU7BranchRuleSpectrumCell S ->
          SU7NoPrimeBranchingSpectrumCell C n
  left_prime_generated :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n}
      (_F : SU7RawBranchingLocalTensorFilter C S)
      (B : SU7BranchRuleSpectrumCell S),
      Nat.Prime B.leftCode
  right_prime_generated :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n}
      (_F : SU7RawBranchingLocalTensorFilter C S)
      (B : SU7BranchRuleSpectrumCell S),
      Nat.Prime B.rightCode
  prime_edge_projection :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n},
      SU7RawBranchingLocalTensorFilter C S ->
        SU7BranchRuleSpectrumCell S ->
          SU7PrimeEdgeBranchCell n
  projection_preserves_residual :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n}
      (F : SU7RawBranchingLocalTensorFilter C S)
      (B : SU7BranchRuleSpectrumCell S),
      branchWeightResidual
          (primeEdgeBranchCell_of_branchRuleSpectrumCell F B) =
        branchRuleSpectrumResidual B
  zero_to_sum :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      (B : SU7BranchRuleSpectrumCell S),
      branchRuleSpectrumResidual B = 0 ->
        B.leftCode + B.rightCode = 2 * n
  zero_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {S : SU7BranchingDecompositionSpectrum n}
      (_F : SU7RawBranchingLocalTensorFilter C S)
      (B : SU7BranchRuleSpectrumCell S),
      branchRuleSpectrumResidual B = 0 ->
        TraceZeroPrimeEdgeLoop n

/-- Canonical P939 branch-rule spectrum projection certificate. -/
def su7BranchRuleSpectrumPrimeEdgeProjectionCertificate :
    SU7BranchRuleSpectrumPrimeEdgeProjectionCertificate where
  cell_to_no_prime := noPrimeBranchingCell_of_branchRuleSpectrumCell
  left_prime_generated := branchRuleSpectrumCell_leftCode_prime
  right_prime_generated := branchRuleSpectrumCell_rightCode_prime
  prime_edge_projection := primeEdgeBranchCell_of_branchRuleSpectrumCell
  projection_preserves_residual := branchWeightResidual_branchRuleProjection_eq
  zero_to_sum := branchRuleSpectrumResidual_zero_to_sum
  zero_to_trace_zero := traceZeroPrimeEdgeLoop_of_branchRuleSpectrumCell


end
end StandardModelConstraint
end SaturationMonoid
