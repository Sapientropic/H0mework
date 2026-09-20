import H0mework.Arithmetic.CodePairs.P943
import H0mework.Arithmetic.ShellSources.P928

/-!
# Proposition 944: a top cell and unit confinement generate active support

P943 still asked for `SU7GeneratedCoverageGapActiveSupport`: every missing
energy shell must be hit by an active upper cell.  This file shows that the
support condition is itself produced by a unit successor law, provided the
spectrum has a top cell at the chosen finite energy bound.

The descent picture is now:

```text
top active cell at maxEnergy
+ no unit permanent holonomy
-> unit successor law
-> every lower shell has an active upper cell
-> active gap support
-> generated coverage
```

So the remaining generated-spectrum producer datum is not a coverage Boolean and
not a Goldbach witness; it is a top residual cell plus confinement.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Unit descent fills lower energy shells -/

/-- From any in-spectrum cell, the unit successor law reaches every lower
residual-energy level. -/
theorem exists_cell_at_energy_of_unitSuccessorLaw_from_cell
    {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
    (Hsucc : SU7RawBranchingSpectrumUnitSuccessorLaw S)
    (start : SU7BranchingDecompositionCell n)
    (hstart : start ∈ S.cells) :
    ∀ k : ℕ,
      k ≤ rawAtomCodeBranchingDecompositionResidualEnergy start ->
        ∃ c : SU7BranchingDecompositionCell n,
          c ∈ S.cells ∧
            rawAtomCodeBranchingDecompositionResidualEnergy c = k := by
  let E (c : SU7BranchingDecompositionCell n) :=
    rawAtomCodeBranchingDecompositionResidualEnergy c
  let motive (e : ℕ) : Prop :=
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ S.cells ->
        E c = e ->
          ∀ k : ℕ, k ≤ e ->
            ∃ z : SU7BranchingDecompositionCell n,
              z ∈ S.cells ∧ E z = k
  have hmain : ∀ e : ℕ, motive e := by
    intro e
    refine Nat.strong_induction_on e ?_
    intro e ih c hmem hE k hkle
    by_cases hk : k = e
    · exact ⟨c, hmem, by simpa [E, hk] using hE⟩
    · have hklt : k < e := Nat.lt_of_le_of_ne hkle hk
      have hepos : 0 < e := by omega
      have hnonzero :
          rawAtomCodeBranchingDecompositionResidual c ≠ 0 := by
        intro hzero
        have hEzero : E c = 0 := by
          dsimp [E]
          exact
            (rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
              c).mpr hzero
        omega
      rcases Hsucc c hmem hnonzero with ⟨next, hnext_mem, hnext_E⟩
      have hsucc : E next + 1 = e := by
        change rawAtomCodeBranchingDecompositionResidualEnergy next + 1 = e
        rw [hnext_E]
        simpa [E] using hE
      have hnext_E_pred : E next = e - 1 := by
        omega
      have hnext_lt : E next < e := by omega
      have hk_next : k ≤ E next := by omega
      exact ih (E next) hnext_lt next hnext_mem rfl k hk_next
  intro k hk
  exact hmain (E start) start hstart rfl k hk

/-- A unit-confining spectrum with a top cell produces active support for all
possible generated coverage gaps below the top energy. -/
theorem activeSupport_of_forbidsUnitPermanentHolonomy_and_topCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (start : SU7BranchingDecompositionCell n)
    (hstart : start ∈ S.cells)
    (htop :
      rawAtomCodeBranchingDecompositionResidualEnergy start = maxEnergy)
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S) :
    SU7GeneratedCoverageGapActiveSupport S maxEnergy := by
  have Hsucc : SU7RawBranchingSpectrumUnitSuccessorLaw S :=
    (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw S).mp hforbid
  refine { upper_of_gap := ?_ }
  intro gap
  have hle_max : gap.level + 1 ≤ maxEnergy :=
    Nat.succ_le_iff.mpr gap.level_lt
  have hle :
      gap.level + 1 ≤
        rawAtomCodeBranchingDecompositionResidualEnergy start := by
    rw [htop]
    exact hle_max
  rcases
      exists_cell_at_energy_of_unitSuccessorLaw_from_cell
        Hsucc start hstart (gap.level + 1) hle with
    ⟨upperCell, hmem, henergy⟩
  have hnonzero :
      rawAtomCodeBranchingDecompositionResidual upperCell ≠ 0 := by
    intro hzero
    have hEzero :
        rawAtomCodeBranchingDecompositionResidualEnergy upperCell = 0 :=
      (rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
        upperCell).mpr hzero
    omega
  exact ⟨upperCell, hmem, hnonzero, henergy⟩

/-- A unit-confining spectrum with a top cell has a true generated coverage
check. -/
theorem coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_topCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (maxEnergy : ℕ)
    (start : SU7BranchingDecompositionCell n)
    (hstart : start ∈ S.cells)
    (htop :
      rawAtomCodeBranchingDecompositionResidualEnergy start = maxEnergy)
    (hforbid : SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S) :
    rawBranchingEnergyShellCoverageCheck S maxEnergy = true :=
  coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_activeSupport
    S maxEnergy hforbid
    (activeSupport_of_forbidsUnitPermanentHolonomy_and_topCell
      S maxEnergy start hstart htop hforbid)

/-! ## Generated top-confinement certificates -/

/-- A generated raw branching certificate whose coverage is produced from a
top residual cell and unit-holonomy confinement. -/
structure SU7GeneratedBooleanRawBranchingTopConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  startCell : SU7BranchingDecompositionCell n
  start_mem :
    startCell ∈
      (booleanGeneratedRawBranchingSpectrum n codeBound).cells
  start_energy_top :
    rawAtomCodeBranchingDecompositionResidualEnergy startCell =
      generatedRawBranchingMaxEnergy n codeBound
  forbids_unit_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n codeBound)

/-- A top-confinement certificate produces the P943 confinement coverage
certificate. -/
def confinementCoverageCertificate_of_topConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingTopConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingConfinementCoverageCertificate n where
  codeBound := G.codeBound
  startCell := G.startCell
  start_mem := G.start_mem
  forbids_unit_permanent_holonomy :=
    G.forbids_unit_permanent_holonomy
  active_gap_support :=
    activeSupport_of_forbidsUnitPermanentHolonomy_and_topCell
      (booleanGeneratedRawBranchingSpectrum n G.codeBound)
      (generatedRawBranchingMaxEnergy n G.codeBound)
      G.startCell G.start_mem G.start_energy_top
      G.forbids_unit_permanent_holonomy

/-- A top-confinement certificate produces the transparent generated raw shell
coverage theorem directly.  The generated Boolean coverage certificate can be
rebuilt later from this shell law and the canonical `(2, 2)` start cell, so
the top cell is not a separate start-witness producer for P1048. -/
theorem generatedRawEnergyCoverage_of_topConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingTopConfinementCertificate n) :
    GeneratedRawEnergyCoverage n G.codeBound :=
  (generatedCoverageCheck_iff_energyCoverage n G.codeBound).mp
    (coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_topCell
      (booleanGeneratedRawBranchingSpectrum n G.codeBound)
      (generatedRawBranchingMaxEnergy n G.codeBound)
      G.startCell G.start_mem G.start_energy_top
      G.forbids_unit_permanent_holonomy)

/-- A top-confinement certificate produces a no-gap certificate. -/
def noGapCertificate_of_topConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingTopConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingNoGapCertificate n :=
  noGapCertificate_of_confinementCoverageCertificate
    (confinementCoverageCertificate_of_topConfinementCertificate G)

/-- A top-confinement certificate computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_topConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingTopConfinementCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_confinementCoverageCertificate
    (confinementCoverageCertificate_of_topConfinementCertificate G)

/-- Every even fiber carries a generated top-confinement certificate. -/
def SU7GeneratedTopConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedBooleanRawBranchingTopConfinementCertificate n)

/-- Fiberwise top confinement gives ordinary even Goldbach. -/
theorem evenGoldbach_of_generatedTopConfinement
    (H : SU7GeneratedTopConfinementEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedConfinementCoverage
    (by
      intro n hn
      exact
        ⟨confinementCoverageCertificate_of_topConfinementCertificate
          (Classical.choice (H n hn))⟩)

/-! ## Certificate -/

/-- P944 certificate: top residual cells and unit-holonomy confinement generate
active support and therefore generated coverage. -/
structure SU7GeneratedTopConfinementProducerCertificate where
  unit_descent_fills_lower_shells :
    ∀ {n : ℕ} {S : SU7BranchingDecompositionSpectrum n}
      (_Hsucc : SU7RawBranchingSpectrumUnitSuccessorLaw S)
      (start : SU7BranchingDecompositionCell n),
      start ∈ S.cells ->
        ∀ k : ℕ,
          k ≤ rawAtomCodeBranchingDecompositionResidualEnergy start ->
            ∃ c : SU7BranchingDecompositionCell n,
              c ∈ S.cells ∧
                rawAtomCodeBranchingDecompositionResidualEnergy c = k
  top_confinement_to_active_support :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ)
      (start : SU7BranchingDecompositionCell n),
      start ∈ S.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy start = maxEnergy ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ->
            SU7GeneratedCoverageGapActiveSupport S maxEnergy
  top_confinement_to_coverage_check :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      (maxEnergy : ℕ)
      (start : SU7BranchingDecompositionCell n),
      start ∈ S.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy start = maxEnergy ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy S ->
            rawBranchingEnergyShellCoverageCheck S maxEnergy = true
  top_confinement_to_raw_energy_coverage :
    ∀ {n : ℕ}
      (G : SU7GeneratedBooleanRawBranchingTopConfinementCertificate n),
        GeneratedRawEnergyCoverage n G.codeBound
  top_confinement_to_no_gap :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingTopConfinementCertificate n ->
        SU7GeneratedBooleanRawBranchingNoGapCertificate n
  top_confinement_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingTopConfinementCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedTopConfinementEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P944 generated top-confinement producer certificate. -/
def su7GeneratedTopConfinementProducerCertificate :
    SU7GeneratedTopConfinementProducerCertificate where
  unit_descent_fills_lower_shells :=
    exists_cell_at_energy_of_unitSuccessorLaw_from_cell
  top_confinement_to_active_support :=
    activeSupport_of_forbidsUnitPermanentHolonomy_and_topCell
  top_confinement_to_coverage_check :=
    coverageCheck_true_of_forbidsUnitPermanentHolonomy_and_topCell
  top_confinement_to_raw_energy_coverage :=
    generatedRawEnergyCoverage_of_topConfinementCertificate
  top_confinement_to_no_gap :=
    noGapCertificate_of_topConfinementCertificate
  top_confinement_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_topConfinementCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedTopConfinement


end
end StandardModelConstraint
end SaturationMonoid
