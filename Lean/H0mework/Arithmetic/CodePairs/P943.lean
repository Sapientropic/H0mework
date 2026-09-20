import H0mework.Arithmetic.CodePairs.P942

/-!
# Proposition 943: confinement plus active gap support gives generated coverage

P942 proved the local obstruction bridge:

```text
coverage gap + active upper cell -> unit permanent holonomy
```

This file turns that local bridge into a coverage producer.  If every possible
missing shell would be hit by an active upper cell, then forbidding unit
permanent holonomy forbids all coverage gaps.  By P941, the Boolean coverage
check is therefore true.

This is the first generated-spectrum route where coverage is produced from
confinement dynamics rather than stored as a raw Boolean field.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Active support for missing shells -/

/-- Every generated coverage gap, if present, is hit by an active cell one
energy unit above the missing shell. -/
structure SU7GeneratedCoverageGapActiveSupport
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) where
  upper_of_gap :
    ∀ gap : SU7GeneratedSpectrumCoverageGap S maxEnergy,
      ∃ upperCell : SU7BranchingDecompositionCell n,
        upperCell ∈ S.cells ∧
          rawAtomCodeBranchingDecompositionResidual upperCell ≠ 0 ∧
            rawAtomCodeBranchingDecompositionResidualEnergy upperCell =
              gap.level + 1

/-- Active support packages any gap into the P942 gap-upper-cell obstruction
configuration. -/
def coverageGapUpperCell_of_activeSupport
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    {maxEnergy : ℕ}
    (A : SU7GeneratedCoverageGapActiveSupport S maxEnergy)
    (gap : SU7GeneratedSpectrumCoverageGap S maxEnergy) :
    SU7GeneratedCoverageGapUpperCell S maxEnergy :=
  let upperCell := Classical.choose (A.upper_of_gap gap)
  let hspec := Classical.choose_spec (A.upper_of_gap gap)
  { gap := gap
    upperCell := upperCell
    upper_mem := hspec.1
    upper_nonzero := hspec.2.1
    upper_energy := hspec.2.2 }

/-! ## Confinement produces no-gap coverage -/

/-- If every gap is active and unit permanent holonomy is forbidden, then no
coverage gap can exist. -/
theorem forbidsCoverageGap_of_forbidsUnitPermanentHolonomy_and_activeSupport
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S)
    (A : SU7GeneratedCoverageGapActiveSupport S maxEnergy) :
    SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy := by
  intro gap
  exact forbidsUnitPermanentHolonomy_forbidsCoverageGapUpperCell
    hforbid (coverageGapUpperCell_of_activeSupport A gap)

/-- Confinement plus active support turns the executable coverage checker true.
-/
theorem coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_activeSupport
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S)
    (A : SU7GeneratedCoverageGapActiveSupport S maxEnergy) :
    rawBranchingEnergyShellCoverageCheck S maxEnergy = true :=
  (rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
    S maxEnergy).mpr
      (forbidsCoverageGap_of_forbidsUnitPermanentHolonomy_and_activeSupport
        S maxEnergy hforbid A)

/-! ## Generated-spectrum confinement certificates -/

/-- A generated raw branching certificate whose coverage is produced by
confinement and active gap support, not stored as a Boolean receipt. -/
structure SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate
    (n : ℕ) where
  codeBound : ℕ
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈
      (booleanGeneratedRawBranchingSpectrum n codeBound).cells
  forbids_unit_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n codeBound)
  active_gap_support :
    SU7GeneratedCoverageGapActiveSupport
      (booleanGeneratedRawBranchingSpectrum n codeBound)
      (generatedRawBranchingMaxEnergy n codeBound)

/-- Generated confinement coverage gives the P941 no-gap certificate. -/
def noGapCertificate_of_confinementCoverageCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n) :
    SU7GeneratedBooleanRawBranchingNoGapCertificate n where
  codeBound := G.codeBound
  startCell := G.startCell
  start_mem := G.start_mem
  forbids_coverage_gap :=
    forbidsCoverageGap_of_forbidsUnitPermanentHolonomy_and_activeSupport
      (booleanGeneratedRawBranchingSpectrum n G.codeBound)
      (generatedRawBranchingMaxEnergy n G.codeBound)
      G.forbids_unit_permanent_holonomy
      G.active_gap_support

/-- Generated confinement coverage gives the older generated coverage
certificate, but now the coverage field is produced by the gap/holonomy bridge.
-/
def generatedCoverageCertificate_of_confinementCoverageCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n) :
    SU7GeneratedBooleanRawBranchingCoverageCertificate n :=
  generatedCoverageCertificate_of_noGapCertificate
    (noGapCertificate_of_confinementCoverageCertificate G)

/-- Generated confinement coverage computes a trace-zero prime-edge loop
through the P941 -> P940 -> P939 no-smuggling route. -/
def traceZeroPrimeEdgeLoop_of_confinementCoverageCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedNoGapCertificate
    (noGapCertificate_of_confinementCoverageCertificate G)

/-- Every even fiber carries a generated confinement coverage certificate. -/
def SU7GeneratedConfinementCoverageEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty
      (SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n)

/-- Fiberwise generated confinement coverage gives ordinary even Goldbach. -/
theorem evenGoldbach_of_generatedConfinementCoverage
    (H : SU7GeneratedConfinementCoverageEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedNoGapCertificates
    (by
      intro n hn
      exact ⟨noGapCertificate_of_confinementCoverageCertificate
        (Classical.choice (H n hn))⟩)

/-! ## Certificate -/

/-- P943 certificate: active-gap support plus unit-holonomy confinement
produces executable generated coverage. -/
structure SU7GeneratedConfinementCoverageProducerCertificate where
  active_gap_to_gap_upper :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      {maxEnergy : ℕ},
      SU7GeneratedCoverageGapActiveSupport S maxEnergy ->
        ∀ _gap : SU7GeneratedSpectrumCoverageGap S maxEnergy,
          SU7GeneratedCoverageGapUpperCell S maxEnergy
  confinement_active_support_to_no_gap :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ->
        SU7GeneratedCoverageGapActiveSupport S maxEnergy ->
          SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy
  confinement_active_support_to_coverage_check :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ->
        SU7GeneratedCoverageGapActiveSupport S maxEnergy ->
          rawBranchingEnergyShellCoverageCheck S maxEnergy = true
  generated_confinement_to_no_gap :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n ->
        SU7GeneratedBooleanRawBranchingNoGapCertificate n
  generated_confinement_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedConfinementCoverageEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P943 generated confinement coverage producer certificate. -/
def su7GeneratedConfinementCoverageProducerCertificate :
    SU7GeneratedConfinementCoverageProducerCertificate where
  active_gap_to_gap_upper :=
    coverageGapUpperCell_of_activeSupport
  confinement_active_support_to_no_gap :=
    forbidsCoverageGap_of_forbidsUnitPermanentHolonomy_and_activeSupport
  confinement_active_support_to_coverage_check :=
    coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_activeSupport
  generated_confinement_to_no_gap :=
    noGapCertificate_of_confinementCoverageCertificate
  generated_confinement_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_confinementCoverageCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedConfinementCoverage


end
end StandardModelConstraint
end SaturationMonoid
