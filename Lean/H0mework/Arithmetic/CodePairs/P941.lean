import H0mework.Physics.BranchSources.P940

/-!
# Proposition 941: generated coverage failure is a canonical energy gap

P940 routes a successful generated coverage certificate through the P939
branch-rule projection throat.  The remaining receipt in that route is the
Boolean field:

```lean
rawBranchingEnergyShellCoverageCheck ... = true
```

This file replaces that raw Boolean with its obstruction-theoretic content.  A
failed generated coverage check is exactly a missing residual-energy shell in
the finite SU(7) branch spectrum.  Forbidding that missing-shell obstruction
generates the coverage certificate consumed by P940.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Coverage gaps -/

/-- A missing residual-energy shell in a generated raw branch spectrum.

This is the canonical obstruction behind a failed finite generated-coverage
check: some level below the computed bound has no in-spectrum branch cell. -/
structure SU7GeneratedSpectrumCoverageGap
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) where
  level : ℕ
  level_lt : level < maxEnergy
  hasEnergy_false :
    rawBranchingSpectrumHasEnergy S level = false

/-- A generated spectrum forbids coverage gaps when every checked residual
energy shell is represented. -/
def SU7GeneratedSpectrumForbidsCoverageGap
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) : Prop :=
  ∀ _gap : SU7GeneratedSpectrumCoverageGap S maxEnergy, False

/-- A true coverage check is exactly absence of missing energy-shell
obstructions. -/
theorem rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) :
    rawBranchingEnergyShellCoverageCheck S maxEnergy = true ↔
      SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy := by
  constructor
  · intro hcheck gap
    unfold rawBranchingEnergyShellCoverageCheck at hcheck
    have hhas :
        rawBranchingSpectrumHasEnergy S gap.level = true :=
      (List.all_eq_true.mp hcheck) gap.level
        (List.mem_range.mpr gap.level_lt)
    rw [gap.hasEnergy_false] at hhas
    contradiction
  · intro hforbid
    unfold rawBranchingEnergyShellCoverageCheck
    apply List.all_eq_true.mpr
    intro k hk
    cases hhas : rawBranchingSpectrumHasEnergy S k
    · exact False.elim
        (hforbid
          { level := k
            level_lt := List.mem_range.mp hk
            hasEnergy_false := hhas })
    · rfl

/-- A false coverage check is exactly a nonempty missing-shell obstruction.
-/
theorem rawBranchingEnergyShellCoverageCheck_false_iff_gap
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ) :
    rawBranchingEnergyShellCoverageCheck S maxEnergy = false ↔
      Nonempty (SU7GeneratedSpectrumCoverageGap S maxEnergy) := by
  constructor
  · intro hfalse
    by_contra hnone
    have hforbid :
        SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy := by
      intro gap
      exact hnone ⟨gap⟩
    have htrue :
        rawBranchingEnergyShellCoverageCheck S maxEnergy = true :=
      (rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
        S maxEnergy).mpr hforbid
    rw [hfalse] at htrue
    contradiction
  · intro hgap
    cases hcheck :
        rawBranchingEnergyShellCoverageCheck S maxEnergy
    · rfl
    · have hforbid :
          SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy :=
        (rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
          S maxEnergy).mp hcheck
      exact False.elim (hforbid (Classical.choice hgap))

/-! ## No-gap generated certificates -/

/-- A generated raw-branching certificate with the Boolean coverage field
replaced by the canonical no-gap obstruction condition. -/
structure SU7GeneratedBooleanRawBranchingNoGapCertificate
    (n : ℕ) where
  codeBound : ℕ
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈
      (booleanGeneratedRawBranchingSpectrum n codeBound).cells
  forbids_coverage_gap :
    SU7GeneratedSpectrumForbidsCoverageGap
      (booleanGeneratedRawBranchingSpectrum n codeBound)
      (generatedRawBranchingMaxEnergy n codeBound)

/-- A no-gap generated certificate computes the Boolean generated coverage
certificate required by P940. -/
def generatedCoverageCertificate_of_noGapCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNoGapCertificate n) :
    SU7GeneratedBooleanRawBranchingCoverageCertificate n where
  codeBound := G.codeBound
  startCell := G.startCell
  start_mem := G.start_mem
  coverage_check :=
    (rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
      (booleanGeneratedRawBranchingSpectrum n G.codeBound)
      (generatedRawBranchingMaxEnergy n G.codeBound)).mpr
        G.forbids_coverage_gap

/-- The generated coverage certificate reconstructed from no-gap data has the
same code bound. -/
@[simp] theorem generatedCoverageCertificate_of_noGap_codeBound
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNoGapCertificate n) :
    (generatedCoverageCertificate_of_noGapCertificate G).codeBound =
      G.codeBound := rfl

/-- A no-gap generated certificate reaches P940's branch-rule trace-zero
readout. -/
def traceZeroPrimeEdgeLoop_of_generatedNoGapCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNoGapCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedCoverageBranchRule
    (generatedCoverageCertificate_of_noGapCertificate G)

/-- Every even fiber carries a no-gap generated certificate. -/
def SU7GeneratedBooleanRawBranchingNoGapEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedBooleanRawBranchingNoGapCertificate n)

/-- Fiberwise no-gap generated certificates give the P940 generated-coverage
route on every even fiber. -/
def generatedCoverageEveryEvenFiber_of_noGapEveryEvenFiber
    (H : SU7GeneratedBooleanRawBranchingNoGapEveryEvenFiber) :
    SU7GeneratedBooleanRawBranchingCoverageEveryEvenFiber := by
  intro n hn
  exact ⟨generatedCoverageCertificate_of_noGapCertificate
    (Classical.choice (H n hn))⟩

/-- Fiberwise no-gap generated certificates give ordinary even Goldbach through
P941 -> P940 -> P939's branch-rule projection throat. -/
theorem evenGoldbach_of_generatedNoGapCertificates
    (H : SU7GeneratedBooleanRawBranchingNoGapEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedCoverageBranchRule
    (generatedCoverageEveryEvenFiber_of_noGapEveryEvenFiber H)

/-! ## Certificate -/

/-- P941 certificate: generated coverage failure is exactly a finite
residual-energy-shell gap, and forbidding that gap generates the P940 route.
-/
structure SU7GeneratedCoverageGapObstructionCertificate where
  true_iff_no_gap :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      rawBranchingEnergyShellCoverageCheck S maxEnergy = true ↔
        SU7GeneratedSpectrumForbidsCoverageGap S maxEnergy
  false_iff_gap :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ),
      rawBranchingEnergyShellCoverageCheck S maxEnergy = false ↔
        Nonempty (SU7GeneratedSpectrumCoverageGap S maxEnergy)
  no_gap_to_coverage :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingNoGapCertificate n ->
        SU7GeneratedBooleanRawBranchingCoverageCertificate n
  no_gap_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingNoGapCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedBooleanRawBranchingNoGapEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P941 coverage-gap obstruction certificate. -/
def su7GeneratedCoverageGapObstructionCertificate :
    SU7GeneratedCoverageGapObstructionCertificate where
  true_iff_no_gap :=
    rawBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
  false_iff_gap :=
    rawBranchingEnergyShellCoverageCheck_false_iff_gap
  no_gap_to_coverage :=
    generatedCoverageCertificate_of_noGapCertificate
  no_gap_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_generatedNoGapCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedNoGapCertificates


end
end StandardModelConstraint
end SaturationMonoid
