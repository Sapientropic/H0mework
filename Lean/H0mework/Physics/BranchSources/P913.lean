import H0mework.Physics.BranchSources.P912

/-!
# Proposition 913: local branching successor laws generate split repairs

P912 consumes an explicit repair map.  This file removes that stored map.
The new producer is a local branching successor law on the raw SU(7)
branching spectrum: every active nonzero raw residual cell has an allowed
successor cell whose residual energy is lower by exactly one unit.

Choice turns that local successor law into the P912 repair rule.  The branch
cell, not a stored prime pair or stored zero, remains the only computational
object.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Local branching successor laws -/

/-- A local successor law on raw SU(7) branching-decomposition cells.

For every in-spectrum cell with nonzero raw atom-code residual, the branching
spectrum contains a successor cell whose raw residual energy is exactly one
unit lower.  This is the edge-law form of confinement: no active residual can
be terminal. -/
structure SU7RawBranchingLocalSuccessorLaw
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  successor_exists :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          ∃ c' : SU7BranchingDecompositionCell n,
            c' ∈ spectrum.cells ∧
              rawAtomCodeBranchingDecompositionResidualEnergy c' + 1 =
                rawAtomCodeBranchingDecompositionResidualEnergy c

/-- The repair map selected from a local successor law.  Outside the active
spectrum, it is the identity; the producer theorems only use it on cells known
to lie in the spectrum. -/
def rawBranchingSuccessorRepair
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n)
    (c : SU7BranchingDecompositionCell n) :
    SU7BranchingDecompositionCell n :=
  if hmem : c ∈ L.spectrum.cells then
    if hzero : rawAtomCodeBranchingDecompositionResidual c = 0 then
      c
    else
      Classical.choose (L.successor_exists c hmem hzero)
  else
    c

theorem rawBranchingSuccessorRepair_mem_preserves
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ L.spectrum.cells) :
    rawBranchingSuccessorRepair L c ∈ L.spectrum.cells := by
  by_cases hzero : rawAtomCodeBranchingDecompositionResidual c = 0
  · simp [rawBranchingSuccessorRepair, hmem, hzero]
  · have hspec :=
      Classical.choose_spec (L.successor_exists c hmem hzero)
    simpa [rawBranchingSuccessorRepair, hmem, hzero] using hspec.1

theorem rawBranchingSuccessorRepair_fixed_of_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ L.spectrum.cells)
    (hzero : rawAtomCodeBranchingDecompositionResidual c = 0) :
    rawBranchingSuccessorRepair L c = c := by
  simp [rawBranchingSuccessorRepair, hmem, hzero]

theorem rawBranchingSuccessorRepair_energy_split_decrement
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ L.spectrum.cells)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0) :
    rawAtomCodeBranchingDecompositionResidualEnergy
        (rawBranchingSuccessorRepair L c) + 1 =
      rawAtomCodeBranchingDecompositionResidualEnergy c := by
  have hspec :=
    Classical.choose_spec (L.successor_exists c hmem hnonzero)
  simpa [rawBranchingSuccessorRepair, hmem, hnonzero] using hspec.2

/-- A local branching successor law is a P912 residual-split repair rule. -/
def residualSplitRepairRule_of_branchingSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n) :
    SU7RawResidualSplitRepairRule C n where
  spectrum := L.spectrum
  startCell := L.startCell
  start_mem := L.start_mem
  tensor_filter := L.tensor_filter
  repair := rawBranchingSuccessorRepair L
  repair_mem_preserves :=
    rawBranchingSuccessorRepair_mem_preserves L
  repair_fixed_of_zero :=
    rawBranchingSuccessorRepair_fixed_of_zero L
  repair_energy_split_decrement :=
    rawBranchingSuccessorRepair_energy_split_decrement L

/-! ## Generated zero readout -/

/-- A local branching successor law computes a zero raw residual cell. -/
theorem exists_zeroRawCell_of_branchingSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ L.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 :=
  exists_zeroRawCell_of_residualSplitRepairRule
    (residualSplitRepairRule_of_branchingSuccessorLaw L)

/-- A local branching successor law computes a generated P909 physical zero
branch cell. -/
def generatedPhysicalZeroBranchCell_of_branchingSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_residualSplitRepairRule
    (residualSplitRepairRule_of_branchingSuccessorLaw L)

/-- A local branching successor law computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_branchingSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingLocalSuccessorLaw C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_residualSplitRepairRule
    (residualSplitRepairRule_of_branchingSuccessorLaw L)

/-! ## Fiberwise local successor confinement -/

/-- Every even fiber carries a raw local branching successor law. -/
def SU7RawBranchingLocalSuccessorLawEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingLocalSuccessorLaw C n)

/-- Fiberwise local successor laws compute generated physical zero branch
cells on every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_branchingSuccessorLaws
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingLocalSuccessorLawEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_branchingSuccessorLaw
    (Classical.choice (H n hn))

/-- Fiberwise local successor laws compute trace-zero prime-edge loops. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchingSuccessorLaws
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingLocalSuccessorLawEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCellEveryEvenFiber_of_branchingSuccessorLaws
      H n hn)

/-- Fiberwise local successor laws give ordinary even Goldbach through
P912/P911/P909's non-storing physical-cell readout. -/
theorem evenGoldbach_of_branchingSuccessorLaws
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingLocalSuccessorLawEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchingSuccessorLaws H)

/-! ## Certificate -/

/-- P913 certificate: local raw branching successor laws generate split repairs
and hence generated physical zero branch cells. -/
structure SU7RawBranchingLocalSuccessorProducerCertificate where
  successor_repair_mem_preserves :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (L : SU7RawBranchingLocalSuccessorLaw C n)
      (c : SU7BranchingDecompositionCell n),
      c ∈ L.spectrum.cells ->
        rawBranchingSuccessorRepair L c ∈ L.spectrum.cells
  successor_repair_split_decrement :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (L : SU7RawBranchingLocalSuccessorLaw C n)
      (c : SU7BranchingDecompositionCell n),
      c ∈ L.spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          rawAtomCodeBranchingDecompositionResidualEnergy
              (rawBranchingSuccessorRepair L c) + 1 =
            rawAtomCodeBranchingDecompositionResidualEnergy c
  successor_law_to_repair_rule :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingLocalSuccessorLaw C n ->
        SU7RawResidualSplitRepairRule C n
  successor_law_to_zero_raw_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (L : SU7RawBranchingLocalSuccessorLaw C n),
      ∃ z : SU7BranchingDecompositionCell n,
        z ∈ L.spectrum.cells ∧
          rawAtomCodeBranchingDecompositionResidual z = 0
  successor_law_to_generated_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingLocalSuccessorLaw C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  successor_law_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingLocalSuccessorLaw C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingLocalSuccessorLawEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P913 producer certificate. -/
def su7RawBranchingLocalSuccessorProducerCertificate :
    SU7RawBranchingLocalSuccessorProducerCertificate where
  successor_repair_mem_preserves :=
    rawBranchingSuccessorRepair_mem_preserves
  successor_repair_split_decrement :=
    rawBranchingSuccessorRepair_energy_split_decrement
  successor_law_to_repair_rule :=
    residualSplitRepairRule_of_branchingSuccessorLaw
  successor_law_to_zero_raw_cell :=
    exists_zeroRawCell_of_branchingSuccessorLaw
  successor_law_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_branchingSuccessorLaw
  successor_law_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_branchingSuccessorLaw
  every_fiber_to_goldbach :=
    evenGoldbach_of_branchingSuccessorLaws


end
end StandardModelConstraint
end SaturationMonoid
