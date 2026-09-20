import H0mework.Physics.BranchSources.P911

/-!
# Proposition 912: residual-split repair rules generate raw normalizers

P911 consumes a raw branching normalizer whose nonzero steps strictly lower
raw atom-code residual energy.  This file lowers that consumer one more step:
the producer is now a residual-split repair rule.  A repair step does not merely
promise an abstract strict decrease; it certifies the discrete split law

```text
energy_after + 1 = energy_before
```

on every active nonzero raw residual cell.  The P911 normalizer is recovered as
a theorem from that split decrement.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Residual-split repair rules -/

/-- A raw SU(7) branching repair rule with an explicit residual-split
decrement.

This is the next lower producer below P911's normalizer.  It contains no
`Nat.Prime`, no prime exponent data, and no zero cell.  Its only active
dynamics is the one-step energy accounting law: after repairing a nonzero raw
residual cell, the raw residual energy has spent exactly one discrete unit. -/
structure SU7RawResidualSplitRepairRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  repair :
    SU7BranchingDecompositionCell n ->
      SU7BranchingDecompositionCell n
  repair_mem_preserves :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells -> repair c ∈ spectrum.cells
  repair_fixed_of_zero :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c = 0 ->
          repair c = c
  repair_energy_split_decrement :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          rawAtomCodeBranchingDecompositionResidualEnergy (repair c) + 1 =
            rawAtomCodeBranchingDecompositionResidualEnergy c

/-- A split decrement is a strict energy decrease. -/
theorem rawResidualEnergy_decreases_of_split_decrement
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ R.spectrum.cells)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0) :
    rawAtomCodeBranchingDecompositionResidualEnergy (R.repair c) <
      rawAtomCodeBranchingDecompositionResidualEnergy c := by
  have hsplit := R.repair_energy_split_decrement c hmem hnonzero
  omega

/-- A residual-split repair rule is a P911 raw branching normalizer. -/
def rawBranchingNormalizer_of_residualSplitRepairRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n) :
    SU7RawBranchingTensorFilteredNormalizer C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  tensor_filter := R.tensor_filter
  normalize := R.repair
  normalize_mem_preserves := R.repair_mem_preserves
  normalize_strictly_decreases_nonzero := by
    intro c hmem hnonzero
    exact rawResidualEnergy_decreases_of_split_decrement R c hmem hnonzero
  normalize_fixed_of_zero := R.repair_fixed_of_zero

/-! ## Truth formula and zero-cell generation -/

/-- On a residual-split repair rule, fixed point is exactly zero raw residual.
-/
theorem residualSplitRepair_fixed_iff_rawResidual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ R.spectrum.cells) :
    R.repair c = c ↔
      rawAtomCodeBranchingDecompositionResidual c = 0 :=
  rawBranchingNormalizer_fixed_iff_rawResidual_zero
    (rawBranchingNormalizer_of_residualSplitRepairRule R) c hmem

/-- A residual-split repair rule computes a zero raw residual cell. -/
theorem exists_zeroRawCell_of_residualSplitRepairRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ R.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 :=
  exists_zeroRawCell_of_rawBranchingNormalizer
    (rawBranchingNormalizer_of_residualSplitRepairRule R)

/-- A residual-split repair rule computes a generated P909 physical zero branch
cell. -/
def generatedPhysicalZeroBranchCell_of_residualSplitRepairRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_rawBranchingNormalizer
    (rawBranchingNormalizer_of_residualSplitRepairRule R)

/-- A residual-split repair rule computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_residualSplitRepairRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawResidualSplitRepairRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawBranchingNormalizer
    (rawBranchingNormalizer_of_residualSplitRepairRule R)

/-! ## Fiberwise residual-split confinement -/

/-- Every even fiber carries a raw residual-split repair rule. -/
def SU7RawResidualSplitRepairRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawResidualSplitRepairRule C n)

/-- Fiberwise residual-split repair rules compute generated physical zero
branch cells on every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_residualSplitRepairRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawResidualSplitRepairRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_residualSplitRepairRule
    (Classical.choice (H n hn))

/-- Fiberwise residual-split repair rules compute trace-zero prime-edge loops.
-/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_residualSplitRepairRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawResidualSplitRepairRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCellEveryEvenFiber_of_residualSplitRepairRules
      H n hn)

/-- Fiberwise residual-split repair rules give ordinary even Goldbach through
P911/P909's non-storing physical-cell readout. -/
theorem evenGoldbach_of_residualSplitRepairRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawResidualSplitRepairRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_residualSplitRepairRules H)

/-! ## Certificate -/

/-- P912 certificate: explicit residual-split repair rules generate P911 raw
normalizers and hence generated physical zero branch cells. -/
structure SU7RawResidualSplitRepairProducerCertificate where
  split_decrement_decreases :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawResidualSplitRepairRule C n)
      (c : SU7BranchingDecompositionCell n),
      c ∈ R.spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          rawAtomCodeBranchingDecompositionResidualEnergy (R.repair c) <
            rawAtomCodeBranchingDecompositionResidualEnergy c
  repair_rule_to_normalizer :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawResidualSplitRepairRule C n ->
        SU7RawBranchingTensorFilteredNormalizer C n
  fixed_iff_raw_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawResidualSplitRepairRule C n)
      (c : SU7BranchingDecompositionCell n),
      c ∈ R.spectrum.cells ->
        (R.repair c = c ↔
          rawAtomCodeBranchingDecompositionResidual c = 0)
  repair_rule_to_zero_raw_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawResidualSplitRepairRule C n),
      ∃ z : SU7BranchingDecompositionCell n,
        z ∈ R.spectrum.cells ∧
          rawAtomCodeBranchingDecompositionResidual z = 0
  repair_rule_to_generated_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawResidualSplitRepairRule C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  repair_rule_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawResidualSplitRepairRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawResidualSplitRepairRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P912 producer certificate. -/
def su7RawResidualSplitRepairProducerCertificate :
    SU7RawResidualSplitRepairProducerCertificate where
  split_decrement_decreases :=
    rawResidualEnergy_decreases_of_split_decrement
  repair_rule_to_normalizer :=
    rawBranchingNormalizer_of_residualSplitRepairRule
  fixed_iff_raw_zero :=
    residualSplitRepair_fixed_iff_rawResidual_zero
  repair_rule_to_zero_raw_cell :=
    exists_zeroRawCell_of_residualSplitRepairRule
  repair_rule_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_residualSplitRepairRule
  repair_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_residualSplitRepairRule
  every_fiber_to_goldbach :=
    evenGoldbach_of_residualSplitRepairRules


end
end StandardModelConstraint
end SaturationMonoid
