import H0mework.Arithmetic.ShellSources.P917

/-!
# Proposition 918: a finite checker certifies raw energy-shell coverage

P917 lowered the predecessor table to a spectrum-level coverage proposition.
This file makes that proposition computational for finite branch spectra:

```text
check every energy level 0, ..., maxEnergy - 1 appears in the raw spectrum
```

If the Boolean checker returns `true`, Lean derives P917's coverage theorem
and therefore the whole no-gap / trace-zero readout chain.  This is the bridge
where a concrete SU(7) branching-spectrum list can become a proof-producing
producer without storing primes, Goldbach pairs, or predecessor functions.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Boolean energy coverage checker -/

/-- Boolean membership test: does the finite raw branching spectrum contain a
cell with raw residual energy `k`? -/
def rawBranchingSpectrumHasEnergy
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (k : ℕ) : Bool :=
  S.cells.any
    (fun c =>
      decide
        (rawAtomCodeBranchingDecompositionResidualEnergy c = k))

/-- A successful energy-membership check produces an actual in-spectrum cell.
-/
theorem exists_cell_of_rawBranchingSpectrumHasEnergy_eq_true
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (k : ℕ)
    (h : rawBranchingSpectrumHasEnergy S k = true) :
    ∃ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ∧
        rawAtomCodeBranchingDecompositionResidualEnergy c = k := by
  unfold rawBranchingSpectrumHasEnergy at h
  rcases (List.any_eq_true.mp h) with ⟨c, hmem, hc⟩
  exact ⟨c, hmem, (decide_eq_true_eq.mp hc)⟩

/-- Boolean coverage check for all adjacent predecessor energies below the
finite bound.  The checked levels are exactly `0, ..., maxEnergy - 1`. -/
def rawBranchingEnergyShellCoverageCheck
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) : Bool :=
  (List.range maxEnergy).all
    (fun k => rawBranchingSpectrumHasEnergy S k)

/-- A successful Boolean coverage check proves P917's spectrum-level
energy-shell coverage proposition. -/
theorem rawBranchingEnergyShellCoverage_of_check
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (hcheck :
      rawBranchingEnergyShellCoverageCheck S maxEnergy = true) :
    SU7RawBranchingEnergyShellCoverage S maxEnergy := by
  intro e hpos hle
  have hk : e - 1 < maxEnergy := by omega
  have hhas :
      rawBranchingSpectrumHasEnergy S (e - 1) = true :=
    (List.all_eq_true.mp hcheck) (e - 1) (List.mem_range.mpr hk)
  exact exists_cell_of_rawBranchingSpectrumHasEnergy_eq_true
    S (e - 1) hhas

/-! ## Checked spectra generate P917 coverage rules -/

/-- A checked raw branching spectrum.

This is the executable form of P917's coverage rule: it contains the finite
spectrum and a Boolean certificate that every predecessor energy shell is
represented. -/
structure SU7RawBranchingCheckedEnergyShellRule
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
  coverage_check :
    rawBranchingEnergyShellCoverageCheck spectrum maxEnergy = true

/-- A checked finite raw spectrum generates P917's coverage rule. -/
def energyShellCoverageRule_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    SU7RawBranchingEnergyShellCoverageRule C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  tensor_filter := R.tensor_filter
  maxEnergy := R.maxEnergy
  energy_bound := R.energy_bound
  energy_shell_coverage :=
    rawBranchingEnergyShellCoverage_of_check
      R.spectrum R.maxEnergy R.coverage_check

/-- A checked finite raw spectrum generates P910's raw bounded shell. -/
def rawBranchingShell_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    SU7RawBranchingTensorFilteredBoundedEnergyShell C n :=
  rawBranchingShell_of_energyShellCoverageRule
    (energyShellCoverageRule_of_checkedEnergyShellRule R)

/-- A checked finite raw spectrum generates P915 no-gap confinement. -/
def noGapConfinementRule_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingCheckedEnergyShellRule C n) :
    SU7RawBranchingNoGapConfinementRule C n :=
  noGapConfinementRule_of_energyShellCoverageRule
    (energyShellCoverageRule_of_checkedEnergyShellRule R)

/-! ## Fiberwise checked spectra -/

/-- Every even fiber carries a checked raw energy-shell rule. -/
def SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingCheckedEnergyShellRule C n)

/-- Fiberwise checked spectra generate P917 coverage rules on every even
fiber. -/
def energyShellCoverageRulesEveryEvenFiber_of_checkedEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    SU7RawBranchingEnergyShellCoverageRuleEveryEvenFiber C := by
  intro n hn
  exact ⟨energyShellCoverageRule_of_checkedEnergyShellRule
    (Classical.choice (H n hn))⟩

/-- Fiberwise checked spectra generate P910 raw bounded shells on every even
fiber. -/
def rawBranchingShellsEveryEvenFiber_of_checkedEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C :=
  rawBranchingShellsEveryEvenFiber_of_energyShellCoverageRules
    (energyShellCoverageRulesEveryEvenFiber_of_checkedEnergyShellRules H)

/-- Fiberwise checked spectra give ordinary even Goldbach through the explicit
P918 -> P917 -> P916 no-gap route. -/
theorem evenGoldbach_of_checkedEnergyShellRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_energyShellCoverageRules
    (energyShellCoverageRulesEveryEvenFiber_of_checkedEnergyShellRules H)

/-! ## Certificate -/

/-- P918 certificate: a successful finite energy-shell checker generates the
P917 coverage rule and hence the no-gap readout chain. -/
structure SU7RawEnergyShellCheckerProducerCertificate where
  check_true_to_exists_cell :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) (k : ℕ),
      rawBranchingSpectrumHasEnergy S k = true ->
        ∃ c : SU7BranchingDecompositionCell n,
          c ∈ S.cells ∧
            rawAtomCodeBranchingDecompositionResidualEnergy c = k
  check_true_to_coverage :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      rawBranchingEnergyShellCoverageCheck S maxEnergy = true ->
        SU7RawBranchingEnergyShellCoverage S maxEnergy
  checked_rule_to_coverage_rule :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedEnergyShellRule C n ->
        SU7RawBranchingEnergyShellCoverageRule C n
  checked_rule_to_no_gap :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingCheckedEnergyShellRule C n ->
        SU7RawBranchingNoGapConfinementRule C n
  every_fiber_to_raw_shells :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C ->
        SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingCheckedEnergyShellRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P918 checker certificate. -/
def su7RawEnergyShellCheckerProducerCertificate :
    SU7RawEnergyShellCheckerProducerCertificate where
  check_true_to_exists_cell :=
    exists_cell_of_rawBranchingSpectrumHasEnergy_eq_true
  check_true_to_coverage :=
    rawBranchingEnergyShellCoverage_of_check
  checked_rule_to_coverage_rule :=
    energyShellCoverageRule_of_checkedEnergyShellRule
  checked_rule_to_no_gap :=
    noGapConfinementRule_of_checkedEnergyShellRule
  every_fiber_to_raw_shells :=
    rawBranchingShellsEveryEvenFiber_of_checkedEnergyShellRules
  every_fiber_to_goldbach :=
    evenGoldbach_of_checkedEnergyShellRules


end
end StandardModelConstraint
end SaturationMonoid
