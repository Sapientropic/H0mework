import H0mework.Arithmetic.ShellSources.P910

/-!
# Proposition 911: raw branching normalizers generate physical zero cells

P910 lowers P908/P909 to raw atom-code branching bounded shells.  This file
pushes the same throat from a shell table to an actual residual-transport
normalizer on raw branching-decomposition cells.

The normalizer contains no prime fields and no zero cell.  It only says that
inside a finite raw branching spectrum, every active nonzero residual is
transported to strictly lower raw atom-code residual energy, while zero
residual cells are fixed.  Strong induction extracts a zero raw cell, and the
tensor irreducibility filter then turns that generated cell into P909's
non-storing physical branch-cell readout.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Raw branching residual-transport normalizers -/

/-- A residual-transport normalizer on raw branching-decomposition cells,
filtered by tensor irreducibility of endpoint codes.

This is the local dynamics version of the P910 raw bounded shell.  It stores no
prime edge, no `Nat.Prime`, and no Goldbach pair. -/
structure SU7RawBranchingTensorFilteredNormalizer
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  normalize :
    SU7BranchingDecompositionCell n ->
      SU7BranchingDecompositionCell n
  normalize_mem_preserves :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells -> normalize c ∈ spectrum.cells
  normalize_strictly_decreases_nonzero :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          rawAtomCodeBranchingDecompositionResidualEnergy (normalize c) <
            rawAtomCodeBranchingDecompositionResidualEnergy c
  normalize_fixed_of_zero :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c = 0 ->
          normalize c = c

/-- Nonzero raw residual cells cannot be fixed by a raw branching normalizer.
-/
theorem rawBranchingNormalizer_not_fixed_of_nonzero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7RawBranchingTensorFilteredNormalizer C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ N.spectrum.cells)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0) :
    N.normalize c ≠ c := by
  intro hfixed
  have hlt :
      rawAtomCodeBranchingDecompositionResidualEnergy c <
        rawAtomCodeBranchingDecompositionResidualEnergy c := by
    simpa [hfixed] using
      N.normalize_strictly_decreases_nonzero c hmem hnonzero
  exact (Nat.lt_irrefl _) hlt

/-- On raw active spectrum cells, fixed point is exactly zero raw residual. -/
theorem rawBranchingNormalizer_fixed_iff_rawResidual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7RawBranchingTensorFilteredNormalizer C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ N.spectrum.cells) :
    N.normalize c = c ↔
      rawAtomCodeBranchingDecompositionResidual c = 0 := by
  constructor
  · intro hfixed
    by_contra hnonzero
    exact rawBranchingNormalizer_not_fixed_of_nonzero
      N c hmem hnonzero hfixed
  · intro hzero
    exact N.normalize_fixed_of_zero c hmem hzero

/-- A raw branching normalizer computes a zero raw atom-code residual cell. -/
theorem exists_zeroRawCell_of_rawBranchingNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7RawBranchingTensorFilteredNormalizer C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ N.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ N.spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c = e ->
          ∃ z : SU7BranchingDecompositionCell n,
            z ∈ N.spectrum.cells ∧
              rawAtomCodeBranchingDecompositionResidual z = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih c hmem henergy
    by_cases hzero : rawAtomCodeBranchingDecompositionResidual c = 0
    · exact ⟨c, hmem, hzero⟩
    · have hnext_mem : N.normalize c ∈ N.spectrum.cells :=
        N.normalize_mem_preserves c hmem
      have hnext_lt :
          rawAtomCodeBranchingDecompositionResidualEnergy
              (N.normalize c) <
            rawAtomCodeBranchingDecompositionResidualEnergy c :=
        N.normalize_strictly_decreases_nonzero c hmem hzero
      exact ih
        (rawAtomCodeBranchingDecompositionResidualEnergy (N.normalize c))
        (by simpa [henergy] using hnext_lt)
        (N.normalize c) hnext_mem rfl
  have hstart :
      motive
        (rawAtomCodeBranchingDecompositionResidualEnergy N.startCell) :=
    Nat.strong_induction_on
      (rawAtomCodeBranchingDecompositionResidualEnergy N.startCell) hstep
  exact hstart N.startCell N.start_mem rfl

/-! ## From zero raw cells to physical branch-cell readout -/

/-- A zero raw branching cell becomes a generated P909 physical zero branch
cell through the tensor irreducibility filter. -/
def generatedPhysicalZeroBranchCell_of_rawBranchingCell_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (F : SU7BranchingTensorIrreducibilityFilter C n)
    (c : SU7BranchingDecompositionCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual c = 0) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  let B := tensorIrreducibleCell_of_rawBranchingDecompositionCell F c
  { cell := physicalBranchCell_of_tensorIrreducibleCell B
    residual_zero := by
      have htensor :
          tensorIrreducibleBranchingSpectrumResidual B = 0 := by
        change
          tensorIrreducibleBranchingSpectrumResidual
              (tensorIrreducibleCell_of_rawBranchingDecompositionCell F c) =
            0
        simpa [tensorIrreducibleCell_rawResidual_eq F c] using hzero
      simpa [physicalResidual_tensorIrreducibleCell_eq B] using htensor
    left_atomCode_prime :=
      tensorPhysicalBranchCell_left_atomCode_prime B
    right_atomCode_prime :=
      tensorPhysicalBranchCell_right_atomCode_prime B }

/-- A raw branching normalizer computes a generated physical zero branch cell.
-/
def generatedPhysicalZeroBranchCell_of_rawBranchingNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7RawBranchingTensorFilteredNormalizer C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  let z := Classical.choose (exists_zeroRawCell_of_rawBranchingNormalizer N)
  let hz := Classical.choose_spec
    (exists_zeroRawCell_of_rawBranchingNormalizer N)
  generatedPhysicalZeroBranchCell_of_rawBranchingCell_zero
    N.tensor_filter z hz.2

/-- A raw branching normalizer computes a trace-zero prime-edge loop via the
non-storing physical branch-cell projection. -/
def traceZeroPrimeEdgeLoop_of_rawBranchingNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7RawBranchingTensorFilteredNormalizer C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_rawBranchingNormalizer N)

/-! ## Fiberwise raw normalizer confinement -/

/-- Every even fiber carries a raw tensor-filtered branching normalizer. -/
def SU7RawBranchingTensorFilteredNormalizerEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingTensorFilteredNormalizer C n)

/-- Fiberwise raw normalizers compute generated physical zero branch cells on
every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_rawBranchingNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredNormalizerEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_rawBranchingNormalizer
    (Classical.choice (H n hn))

/-- Fiberwise raw normalizers compute trace-zero prime-edge loops on every
even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_rawBranchingNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredNormalizerEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCellEveryEvenFiber_of_rawBranchingNormalizers
      H n hn)

/-- Fiberwise raw normalizers give ordinary even Goldbach through P909's
physical-cell readout. -/
theorem evenGoldbach_of_rawBranchingTensorFilteredNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredNormalizerEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_rawBranchingNormalizers H)

/-! ## Certificate -/

/-- P911 certificate: a raw residual-transport normalizer generates zero raw
cells and then P909 physical branch cells, without a shell table or stored
prime data. -/
structure SU7RawBranchingNormalizerProducerCertificate where
  fixed_iff_raw_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7RawBranchingTensorFilteredNormalizer C n)
      (c : SU7BranchingDecompositionCell n),
      c ∈ N.spectrum.cells ->
        (N.normalize c = c ↔
          rawAtomCodeBranchingDecompositionResidual c = 0)
  normalizer_to_zero_raw_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7RawBranchingTensorFilteredNormalizer C n),
      ∃ z : SU7BranchingDecompositionCell n,
        z ∈ N.spectrum.cells ∧
          rawAtomCodeBranchingDecompositionResidual z = 0
  zero_raw_cell_to_generated_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (_F : SU7BranchingTensorIrreducibilityFilter C n)
      (c : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidual c = 0 ->
        SU7GeneratedPhysicalZeroBranchCell n
  normalizer_to_generated_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingTensorFilteredNormalizer C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  normalizer_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingTensorFilteredNormalizer C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingTensorFilteredNormalizerEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P911 producer certificate. -/
def su7RawBranchingNormalizerProducerCertificate :
    SU7RawBranchingNormalizerProducerCertificate where
  fixed_iff_raw_zero :=
    rawBranchingNormalizer_fixed_iff_rawResidual_zero
  normalizer_to_zero_raw_cell :=
    exists_zeroRawCell_of_rawBranchingNormalizer
  zero_raw_cell_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_rawBranchingCell_zero
  normalizer_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_rawBranchingNormalizer
  normalizer_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawBranchingNormalizer
  every_fiber_to_goldbach :=
    evenGoldbach_of_rawBranchingTensorFilteredNormalizers


end
end StandardModelConstraint
end SaturationMonoid
