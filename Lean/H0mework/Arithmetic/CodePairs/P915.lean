import H0mework.Arithmetic.CodePairs.P914

/-!
# Proposition 915: no-gap descent forbids raw unit holonomy

P914 says that forbidding raw unit permanent holonomy is equivalent to the
one-unit successor law.  This file connects that exact one-unit law to the
more common Lyapunov form:

* every nonzero raw residual cell has some strictly lower-energy successor;
* the raw branching spectrum is unit-dense at the top of every strict descent.

Together they force the one-unit successor required by P914.  This is the
formal no-gap bridge: Lyapunov descent must pass through the adjacent integer
energy shell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Strict descent and unit-density on raw branch spectra -/

/-- Raw strict successor law: every active nonzero raw residual cell has some
in-spectrum successor with strictly lower raw residual energy. -/
def SU7RawBranchingSpectrumStrictSuccessorLaw
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c : SU7BranchingDecompositionCell n,
    c ∈ S.cells ->
      rawAtomCodeBranchingDecompositionResidual c ≠ 0 ->
        ∃ lower : SU7BranchingDecompositionCell n,
          lower ∈ S.cells ∧
            rawAtomCodeBranchingDecompositionResidualEnergy lower <
              rawAtomCodeBranchingDecompositionResidualEnergy c

/-- Unit-density at the top of every strict descent: if the spectrum has any
lower-energy in-spectrum cell below `c`, then it also has an in-spectrum cell
exactly one raw energy unit below `c`. -/
def SU7RawBranchingSpectrumEnergyUnitDensity
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c lower : SU7BranchingDecompositionCell n,
    c ∈ S.cells ->
      lower ∈ S.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy lower <
          rawAtomCodeBranchingDecompositionResidualEnergy c ->
          ∃ step : SU7BranchingDecompositionCell n,
            step ∈ S.cells ∧
              rawAtomCodeBranchingDecompositionResidualEnergy step + 1 =
                rawAtomCodeBranchingDecompositionResidualEnergy c

/-- Strict descent plus unit-density gives P914's one-unit successor law. -/
theorem unitSuccessorLaw_of_strictSuccessorLaw_and_unitDensity
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (Hstrict : SU7RawBranchingSpectrumStrictSuccessorLaw S)
    (Hdense : SU7RawBranchingSpectrumEnergyUnitDensity S) :
    SU7RawBranchingSpectrumUnitSuccessorLaw S := by
  intro c hmem hnonzero
  rcases Hstrict c hmem hnonzero with
    ⟨lower, hlower_mem, hlower_lt⟩
  exact Hdense c lower hmem hlower_mem hlower_lt

/-! ## Strict permanent holonomy -/

/-- Raw strict-permanent-holonomy cell: a nonzero residual cell with no
strictly lower-energy in-spectrum successor. -/
def SU7RawBranchingStrictPermanentHolonomyCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (c : SU7BranchingDecompositionCell n) : Prop :=
  c ∈ S.cells ∧
    rawAtomCodeBranchingDecompositionResidual c ≠ 0 ∧
      ∀ lower : SU7BranchingDecompositionCell n,
        lower ∈ S.cells ->
          ¬ rawAtomCodeBranchingDecompositionResidualEnergy lower <
            rawAtomCodeBranchingDecompositionResidualEnergy c

/-- A raw branching spectrum forbids strict permanent holonomy. -/
def SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c : SU7BranchingDecompositionCell n,
    ¬ SU7RawBranchingStrictPermanentHolonomyCell S c

/-- Forbidding strict permanent holonomy is exactly the strict successor law.
-/
theorem noRawStrictPermanentHolonomy_iff_strictSuccessorLaw
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) :
    SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy S ↔
      SU7RawBranchingSpectrumStrictSuccessorLaw S := by
  constructor
  · intro H c hmem hnonzero
    by_contra hnone
    have hterminal :
        ∀ lower : SU7BranchingDecompositionCell n,
          lower ∈ S.cells ->
            ¬ rawAtomCodeBranchingDecompositionResidualEnergy lower <
              rawAtomCodeBranchingDecompositionResidualEnergy c := by
      intro lower hlower_mem hlower_lt
      exact hnone ⟨lower, hlower_mem, hlower_lt⟩
    exact H c ⟨hmem, hnonzero, hterminal⟩
  · intro H c hperm
    rcases hperm with ⟨hmem, hnonzero, hterminal⟩
    rcases H c hmem hnonzero with ⟨lower, hlower_mem, hlower_lt⟩
    exact hterminal lower hlower_mem hlower_lt

/-- Absence of strict permanent holonomy plus unit-density forbids unit
permanent holonomy. -/
theorem noRawUnitPermanentHolonomy_of_noRawStrict_and_unitDensity
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (Hstrict :
      SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy S)
    (Hdense : SU7RawBranchingSpectrumEnergyUnitDensity S) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S := by
  exact (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw S).mpr
    (unitSuccessorLaw_of_strictSuccessorLaw_and_unitDensity S
      ((noRawStrictPermanentHolonomy_iff_strictSuccessorLaw S).mp Hstrict)
      Hdense)

/-! ## No-gap confinement rules -/

/-- A raw branching confinement rule in Lyapunov/no-gap form.

It stores no one-unit successor edge.  The exact unit successor is produced
from strict no-permanent-holonomy plus unit-density of the raw energy shells. -/
structure SU7RawBranchingNoGapConfinementRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  forbids_strict_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy spectrum
  energy_unit_density :
    SU7RawBranchingSpectrumEnergyUnitDensity spectrum

/-- A no-gap confinement rule generates P914's unit-holonomy confinement rule.
-/
def unitHolonomyConfinementRule_of_noGapConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingNoGapConfinementRule C n) :
    SU7RawBranchingUnitHolonomyConfinementRule C n where
  spectrum := R.spectrum
  startCell := R.startCell
  start_mem := R.start_mem
  tensor_filter := R.tensor_filter
  forbids_unit_permanent_holonomy :=
    noRawUnitPermanentHolonomy_of_noRawStrict_and_unitDensity
      R.spectrum R.forbids_strict_permanent_holonomy
      R.energy_unit_density

/-- A no-gap confinement rule computes a zero raw residual cell. -/
theorem exists_zeroRawCell_of_noGapConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingNoGapConfinementRule C n) :
    ∃ z : SU7BranchingDecompositionCell n,
      z ∈ R.spectrum.cells ∧
        rawAtomCodeBranchingDecompositionResidual z = 0 :=
  exists_zeroRawCell_of_unitHolonomyConfinementRule
    (unitHolonomyConfinementRule_of_noGapConfinementRule R)

/-- A no-gap confinement rule computes a generated P909 physical zero branch
cell. -/
def generatedPhysicalZeroBranchCell_of_noGapConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingNoGapConfinementRule C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_unitHolonomyConfinementRule
    (unitHolonomyConfinementRule_of_noGapConfinementRule R)

/-- A no-gap confinement rule computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_noGapConfinementRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7RawBranchingNoGapConfinementRule C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_unitHolonomyConfinementRule
    (unitHolonomyConfinementRule_of_noGapConfinementRule R)

/-! ## Fiberwise no-gap confinement -/

/-- Every even fiber carries a raw no-gap confinement rule. -/
def SU7RawBranchingNoGapConfinementRuleEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingNoGapConfinementRule C n)

/-- Fiberwise no-gap confinement computes trace-zero prime-edge loops. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_noGapConfinementRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingNoGapConfinementRuleEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_noGapConfinementRule
    (Classical.choice (H n hn))

/-- Fiberwise no-gap confinement gives ordinary even Goldbach through the
P914/P913/P912/P911/P909 readout chain. -/
theorem evenGoldbach_of_noGapConfinementRules
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingNoGapConfinementRuleEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_noGapConfinementRules H)

/-! ## Certificate -/

/-- P915 certificate: strict Lyapunov descent plus raw energy unit-density
forbids raw unit permanent holonomy. -/
structure SU7RawNoGapConfinementProducerCertificate where
  strict_plus_density_to_unit_successor :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n),
      SU7RawBranchingSpectrumStrictSuccessorLaw S ->
        SU7RawBranchingSpectrumEnergyUnitDensity S ->
          SU7RawBranchingSpectrumUnitSuccessorLaw S
  no_strict_holonomy_iff_strict_successor :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n),
      SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy S ↔
        SU7RawBranchingSpectrumStrictSuccessorLaw S
  no_strict_plus_density_to_no_unit :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n),
      SU7RawBranchingSpectrumForbidsStrictPermanentHolonomy S ->
        SU7RawBranchingSpectrumEnergyUnitDensity S ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S
  no_gap_rule_to_unit_rule :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingNoGapConfinementRule C n ->
        SU7RawBranchingUnitHolonomyConfinementRule C n
  no_gap_rule_to_zero_raw_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7RawBranchingNoGapConfinementRule C n),
      ∃ z : SU7BranchingDecompositionCell n,
        z ∈ R.spectrum.cells ∧
          rawAtomCodeBranchingDecompositionResidual z = 0
  no_gap_rule_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingNoGapConfinementRule C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingNoGapConfinementRuleEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P915 producer certificate. -/
def su7RawNoGapConfinementProducerCertificate :
    SU7RawNoGapConfinementProducerCertificate where
  strict_plus_density_to_unit_successor :=
    unitSuccessorLaw_of_strictSuccessorLaw_and_unitDensity
  no_strict_holonomy_iff_strict_successor :=
    noRawStrictPermanentHolonomy_iff_strictSuccessorLaw
  no_strict_plus_density_to_no_unit :=
    noRawUnitPermanentHolonomy_of_noRawStrict_and_unitDensity
  no_gap_rule_to_unit_rule :=
    unitHolonomyConfinementRule_of_noGapConfinementRule
  no_gap_rule_to_zero_raw_cell :=
    exists_zeroRawCell_of_noGapConfinementRule
  no_gap_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_noGapConfinementRule
  every_fiber_to_goldbach :=
    evenGoldbach_of_noGapConfinementRules


end
end StandardModelConstraint
end SaturationMonoid
