import H0mework.Physics.BranchSources.P913

/-!
# Proposition 914: raw unit holonomy is exactly local successor failure

P913 consumes a local branching successor law.  This file names the exact
obstruction to that law at the raw atom-code level:

```text
unit permanent holonomy =
  a nonzero raw residual cell with no in-spectrum successor
  whose energy is lower by exactly one unit
```

Forbidding that obstruction is equivalent to P913's successor law, and thus
generates the same physical zero branch-cell readout without storing primes,
zero cells, repair maps, or normalizers.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Raw unit permanent holonomy -/

/-- A raw unit-permanent-holonomy cell in a branching-decomposition spectrum.

This is the exact obstruction to residual-split repair: the cell is in the
spectrum, has nonzero raw atom-code residual, and no in-spectrum successor
spends one discrete unit of raw residual energy. -/
def SU7RawBranchingUnitPermanentHolonomyCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (c : SU7BranchingDecompositionCell n) : Prop :=
  c ∈ S.cells ∧
    rawAtomCodeBranchingDecompositionResidual c ≠ 0 ∧
      ∀ next : SU7BranchingDecompositionCell n,
        next ∈ S.cells ->
          rawAtomCodeBranchingDecompositionResidualEnergy next + 1 ≠
            rawAtomCodeBranchingDecompositionResidualEnergy c

/-- A raw branching-decomposition spectrum forbids unit permanent holonomy. -/
def SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c : SU7BranchingDecompositionCell n,
    ¬ SU7RawBranchingUnitPermanentHolonomyCell S c

/-- The local successor law used by P913, isolated at the spectrum level. -/
def SU7RawBranchingSpectrumUnitSuccessorLaw
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c : SU7BranchingDecompositionCell n,
    c ∈ S.cells ->
      rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
        ∃ next : SU7BranchingDecompositionCell n,
          next ∈ S.cells ∧
            rawAtomCodeBranchingDecompositionResidualEnergy next + 1 =
              rawAtomCodeBranchingDecompositionResidualEnergy c

/-- Forbidding raw unit permanent holonomy is exactly the unit successor law.
-/
theorem noRawUnitPermanentHolonomy_iff_unitSuccessorLaw
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ↔
      SU7RawBranchingSpectrumUnitSuccessorLaw S := by
  constructor
  · intro H c hmem hnonzero
    by_contra hnone
    have hterminal :
        ∀ next : SU7BranchingDecompositionCell n,
          next ∈ S.cells ->
            rawAtomCodeBranchingDecompositionResidualEnergy next + 1 ≠
              rawAtomCodeBranchingDecompositionResidualEnergy c := by
      intro next hnext_mem hnext_eq
      exact hnone ⟨next, hnext_mem, hnext_eq⟩
    exact H c ⟨hmem, hnonzero, hterminal⟩
  · intro H c hperm
    rcases hperm with ⟨hmem, hnonzero, hterminal⟩
    rcases H c hmem hnonzero with ⟨next, hnext_mem, hnext_eq⟩
    exact hterminal next hnext_mem hnext_eq

/-- A missing unit successor is exactly a raw unit permanent holonomy cell. -/
theorem rawUnitPermanentHolonomyCell_of_no_unit_successor
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {c : SU7BranchingDecompositionCell n}
    (hmem : c ∈ S.cells)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0)
    (hterminal :
      ∀ next : SU7BranchingDecompositionCell n,
        next ∈ S.cells ->
          rawAtomCodeBranchingDecompositionResidualEnergy next + 1 ≠
            rawAtomCodeBranchingDecompositionResidualEnergy c) :
    SU7RawBranchingUnitPermanentHolonomyCell S c :=
  ⟨hmem, hnonzero, hterminal⟩

/-- Absence of raw unit permanent holonomy extracts a one-unit successor. -/
theorem unit_successor_of_noRawUnitPermanentHolonomy
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (H : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S)
    (c : SU7BranchingDecompositionCell n)
    (hmem : c ∈ S.cells)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0) :
    ∃ next : SU7BranchingDecompositionCell n,
      next ∈ S.cells ∧
        rawAtomCodeBranchingDecompositionResidualEnergy next + 1 =
          rawAtomCodeBranchingDecompositionResidualEnergy c :=
  (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw S).mp H
    c hmem hnonzero

/-! ## Holonomy-form local successor rules -/

/-- A raw branching rule stated as unit-holonomy elimination. -/
structure SU7RawBranchingUnitHolonomyConfinementRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  forbids_unit_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy spectrum

/-- A unit-holonomy confinement rule generates P913's local successor law. -/
def branchingSuccessorLaw_of_unitHolonomyConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingUnitHolonomyConfinementRule C n) :
    SU7RawBranchingLocalSuccessorLaw C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  tensor_filter := R.tensor_filter
  successor_exists := by
    intro c hmem hnonzero
    exact unit_successor_of_noRawUnitPermanentHolonomy
      R.forbids_unit_permanent_holonomy c hmem hnonzero

/-- A unit-holonomy confinement rule computes a zero raw residual cell. -/
theorem exists_zeroRawCell_of_unitHolonomyConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingUnitHolonomyConfinementRule C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ R.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 :=
  exists_zeroRawCell_of_branchingSuccessorLaw
    (branchingSuccessorLaw_of_unitHolonomyConfinementRule R)

/-- A unit-holonomy confinement rule computes a generated P909 physical zero
branch cell. -/
def generatedPhysicalZeroBranchCell_of_unitHolonomyConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingUnitHolonomyConfinementRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_branchingSuccessorLaw
    (branchingSuccessorLaw_of_unitHolonomyConfinementRule R)

/-- A unit-holonomy confinement rule computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_unitHolonomyConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingUnitHolonomyConfinementRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchingSuccessorLaw
    (branchingSuccessorLaw_of_unitHolonomyConfinementRule R)

/-! ## Fiberwise unit-holonomy confinement -/

/-- Every even fiber carries a raw unit-holonomy confinement rule. -/
def SU7RawBranchingUnitHolonomyConfinementRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingUnitHolonomyConfinementRule C n)

/-- Fiberwise unit-holonomy confinement computes generated physical zero
branch cells on every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_unitHolonomyRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingUnitHolonomyConfinementRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_unitHolonomyConfinementRule
    (Classical.choice (H n hn))

/-- Fiberwise unit-holonomy confinement computes trace-zero prime-edge loops.
-/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_unitHolonomyRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingUnitHolonomyConfinementRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCellEveryEvenFiber_of_unitHolonomyRules
      H n hn)

/-- Fiberwise unit-holonomy confinement gives ordinary even Goldbach through
P913/P912/P911/P909's non-storing physical-cell readout. -/
theorem evenGoldbach_of_unitHolonomyConfinementRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingUnitHolonomyConfinementRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_unitHolonomyRules H)

/-! ## Certificate -/

/-- P914 certificate: raw unit permanent holonomy is exactly failure of the
local one-unit successor law. -/
structure SU7RawUnitHolonomyProducerCertificate where
  no_unit_holonomy_iff_successor :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ↔
        SU7RawBranchingSpectrumUnitSuccessorLaw S
  no_successor_to_holonomy_cell :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {c : SU7BranchingDecompositionCell n},
      c ∈ S.cells ->
        rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
          (∀ next : SU7BranchingDecompositionCell n,
            next ∈ S.cells ->
              rawAtomCodeBranchingDecompositionResidualEnergy next + 1 ≠
                rawAtomCodeBranchingDecompositionResidualEnergy c) ->
            SU7RawBranchingUnitPermanentHolonomyCell S c
  unit_rule_to_successor_law :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingUnitHolonomyConfinementRule C n ->
        SU7RawBranchingLocalSuccessorLaw C n
  unit_rule_to_zero_raw_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingUnitHolonomyConfinementRule C n),
      ∃ z : SU7BranchingDecompositionCell n,
        z ∈ R.spectrum.cells ∧
          rawAtomCodeBranchingDecompositionResidual z = 0
  unit_rule_to_generated_physical :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingUnitHolonomyConfinementRule C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  unit_rule_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingUnitHolonomyConfinementRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingUnitHolonomyConfinementRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P914 producer certificate. -/
def su7RawUnitHolonomyProducerCertificate :
    SU7RawUnitHolonomyProducerCertificate where
  no_unit_holonomy_iff_successor :=
    noRawUnitPermanentHolonomy_iff_unitSuccessorLaw
  no_successor_to_holonomy_cell := by
    intro n S c hmem hnonzero hterminal
    exact rawUnitPermanentHolonomyCell_of_no_unit_successor
      hmem hnonzero hterminal
  unit_rule_to_successor_law :=
    branchingSuccessorLaw_of_unitHolonomyConfinementRule
  unit_rule_to_zero_raw_cell :=
    exists_zeroRawCell_of_unitHolonomyConfinementRule
  unit_rule_to_generated_physical :=
    generatedPhysicalZeroBranchCell_of_unitHolonomyConfinementRule
  unit_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_unitHolonomyConfinementRule
  every_fiber_to_goldbach :=
    evenGoldbach_of_unitHolonomyConfinementRules


end
end StandardModelConstraint
end SaturationMonoid
