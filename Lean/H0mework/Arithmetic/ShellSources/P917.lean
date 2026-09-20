import H0mework.Arithmetic.ShellSources.P916

/-!
# Proposition 917: energy-shell coverage generates raw bounded shells

P916 consumes P910's raw bounded shell, whose strongest field is a concrete
`lowerEnergyCell` function.  This file lowers that input one step: instead of
storing a predecessor function, the producer may give a spectrum-level coverage
property saying that every positive energy shell below the bound is represented
inside the raw SU(7) branching spectrum.

Classical choice then extracts the predecessor function required by P910.
The remaining hard producer is therefore a representation-theoretic coverage
calculation on the finite branching spectrum, not a stored Goldbach witness and
not a stored repair table.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Energy-shell coverage -/

/-- Raw energy-shell coverage for a finite branching spectrum.

For every positive raw residual-energy level `e` within the chosen finite
bound, the spectrum contains a cell at the adjacent predecessor energy
`e - 1`.  This is the spectrum-level no-gap datum that generates P910's
`lowerEnergyCell` field. -/
def SU7RawBranchingEnergyShellCoverage
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) : Prop :=
  ∀ e : ℕ, 0 < e -> e ≤ maxEnergy ->
    ∃ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ∧
        rawAtomCodeBranchingDecompositionResidualEnergy c = e - 1

/-- The predecessor cell selected from energy-shell coverage. -/
def rawBranchingEnergyShellCoverageCell
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (H : SU7RawBranchingEnergyShellCoverage S maxEnergy)
    (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy) :
    SU7BranchingDecompositionCell n :=
  Classical.choose (H e hpos hle)

/-- The selected predecessor cell is in the spectrum. -/
theorem rawBranchingEnergyShellCoverageCell_mem
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (H : SU7RawBranchingEnergyShellCoverage S maxEnergy)
    (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy) :
    rawBranchingEnergyShellCoverageCell H e hpos hle ∈ S.cells := by
  exact (Classical.choose_spec (H e hpos hle)).1

/-- The selected predecessor cell has raw energy exactly `e - 1`. -/
theorem rawBranchingEnergyShellCoverageCell_rawEnergy_eq_pred
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (H : SU7RawBranchingEnergyShellCoverage S maxEnergy)
    (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy) :
    rawAtomCodeBranchingDecompositionResidualEnergy
        (rawBranchingEnergyShellCoverageCell H e hpos hle) = e - 1 := by
  exact (Classical.choose_spec (H e hpos hle)).2

/-! ## Coverage rules generate P910 raw bounded shells -/

/-- A raw branching shell generated from a spectrum-level coverage law.

This object does not store predecessor cells as primitive fields.  It stores
only the raw spectrum, a bound, tensor irreducibility of endpoint codes, and the
coverage property from which predecessor representatives are selected. -/
structure SU7RawBranchingEnergyShellCoverageRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  energy_shell_coverage :
    SU7RawBranchingEnergyShellCoverage spectrum maxEnergy

/-- Energy-shell coverage generates P910's raw bounded shell by selecting
predecessor representatives from the spectrum. -/
def rawBranchingShell_of_energyShellCoverageRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingEnergyShellCoverageRule C n) :
    SU7RawBranchingTensorFilteredBoundedEnergyShell C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  tensor_filter := R.tensor_filter
  maxEnergy := R.maxEnergy
  energy_bound := R.energy_bound
  lowerEnergyCell :=
    rawBranchingEnergyShellCoverageCell R.energy_shell_coverage
  lowerEnergyCell_mem :=
    rawBranchingEnergyShellCoverageCell_mem R.energy_shell_coverage
  lowerEnergyCell_rawEnergy_eq_pred :=
    rawBranchingEnergyShellCoverageCell_rawEnergy_eq_pred
      R.energy_shell_coverage

/-- Energy-shell coverage generates P915 no-gap confinement through P916. -/
def noGapConfinementRule_of_energyShellCoverageRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingEnergyShellCoverageRule C n) :
    SU7RawBranchingNoGapConfinementRule C n :=
  noGapConfinementRule_of_rawBranchingShell
    (rawBranchingShell_of_energyShellCoverageRule R)

/-- Energy-shell coverage computes a trace-zero prime-edge loop through the
P917 -> P916 -> P915 route. -/
def traceZeroPrimeEdgeLoop_of_energyShellCoverageRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingEnergyShellCoverageRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawBranchingShell_viaNoGap
    (rawBranchingShell_of_energyShellCoverageRule R)

/-! ## Fiberwise coverage -/

/-- Every even fiber carries a raw energy-shell coverage rule. -/
def SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingEnergyShellCoverageRule C n)

/-- Fiberwise energy-shell coverage generates P916 raw bounded shells on
every even fiber. -/
def rawBranchingShellsEveryEvenFiber_of_energyShellCoverageRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C) :
    SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C := by
  intro n hn
  exact ⟨rawBranchingShell_of_energyShellCoverageRule
    (Classical.choice (H n hn))⟩

/-- Fiberwise energy-shell coverage generates no-gap confinement rules on
every even fiber. -/
def noGapConfinementRulesEveryEvenFiber_of_energyShellCoverageRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C) :
    SU7RawBranchingNoGapConfinementRuleEveryEvenFiber C :=
  noGapConfinementRulesEveryEvenFiber_of_rawBranchingShells
    (rawBranchingShellsEveryEvenFiber_of_energyShellCoverageRules H)

/-- Fiberwise energy-shell coverage gives ordinary even Goldbach through the
explicit no-gap route. -/
theorem evenGoldbach_of_energyShellCoverageRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_rawBranchingShells_viaNoGap
    (rawBranchingShellsEveryEvenFiber_of_energyShellCoverageRules H)

/-! ## Certificate -/

/-- P917 certificate: spectrum-level energy-shell coverage generates P910 raw
bounded shells and therefore P915 no-gap confinement. -/
structure SU7RawEnergyShellCoverageProducerCertificate where
  coverage_cell_mem :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {maxEnergy : ℕ}
      (H : SU7RawBranchingEnergyShellCoverage S maxEnergy)
      (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      rawBranchingEnergyShellCoverageCell H e hpos hle ∈ S.cells
  coverage_cell_energy_eq_pred :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {maxEnergy : ℕ}
      (H : SU7RawBranchingEnergyShellCoverage S maxEnergy)
      (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      rawAtomCodeBranchingDecompositionResidualEnergy
          (rawBranchingEnergyShellCoverageCell H e hpos hle) = e - 1
  coverage_rule_to_raw_shell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingEnergyShellCoverageRule C n ->
        SU7RawBranchingTensorFilteredBoundedEnergyShell C n
  coverage_rule_to_no_gap :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingEnergyShellCoverageRule C n ->
        SU7RawBranchingNoGapConfinementRule C n
  coverage_rule_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingEnergyShellCoverageRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_raw_shells :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C ->
        SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P917 producer certificate. -/
def su7RawEnergyShellCoverageProducerCertificate :
    SU7RawEnergyShellCoverageProducerCertificate where
  coverage_cell_mem :=
    rawBranchingEnergyShellCoverageCell_mem
  coverage_cell_energy_eq_pred :=
    rawBranchingEnergyShellCoverageCell_rawEnergy_eq_pred
  coverage_rule_to_raw_shell :=
    rawBranchingShell_of_energyShellCoverageRule
  coverage_rule_to_no_gap :=
    noGapConfinementRule_of_energyShellCoverageRule
  coverage_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_energyShellCoverageRule
  every_fiber_to_raw_shells :=
    rawBranchingShellsEveryEvenFiber_of_energyShellCoverageRules
  every_fiber_to_goldbach :=
    evenGoldbach_of_energyShellCoverageRules


end
end StandardModelConstraint
end SaturationMonoid
