import H0mework.Arithmetic.ShellSources.P957

/-!
# Proposition 958: no-prime top confinement produces coverage

P957 made endpoint-coverage failure confinement-visible: a missing shell plus
an active upper cell produces unit permanent holonomy.  This file removes the
active-support field on the no-prime source list itself.

If a finite no-prime branch-cell list has a top endpoint-energy cell and unit
permanent holonomy is forbidden, unit descent fills every lower endpoint-energy
shell.  Therefore the endpoint coverage checker must be true.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Unit descent fills no-prime endpoint-energy shells -/

/-- From any no-prime source cell, the unit successor law reaches every lower
endpoint residual-energy level. -/
theorem exists_noPrimeCell_at_energy_of_unitSuccessorLaw_from_cell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (Hsucc : NoPrimeBranchingCellUnitSuccessorLaw xs)
    (start : SU7NoPrimeBranchingSpectrumCell C n)
    (hstart : start ∈ xs) :
    ∀ k : ℕ,
      k ≤ noPrimeBranchingEndpointResidualEnergy start ->
        ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs ∧ noPrimeBranchingEndpointResidualEnergy B = k := by
  let E (B : SU7NoPrimeBranchingSpectrumCell C n) :=
    noPrimeBranchingEndpointResidualEnergy B
  let motive (e : ℕ) : Prop :=
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ xs ->
        E B = e ->
          ∀ k : ℕ, k ≤ e ->
            ∃ z : SU7NoPrimeBranchingSpectrumCell C n,
              z ∈ xs ∧ E z = k
  have hmain : ∀ e : ℕ, motive e := by
    intro e
    refine Nat.strong_induction_on e ?_
    intro e ih B hmem hE k hkle
    by_cases hk : k = e
    · exact ⟨B, hmem, by simpa [E, hk] using hE⟩
    · have hklt : k < e := Nat.lt_of_le_of_ne hkle hk
      have hnonzero : E B ≠ 0 := by
        intro hzero
        omega
      rcases Hsucc B hmem hnonzero with ⟨next, hnext_mem, hnext_E⟩
      have hnext_E_pred : E next = e - 1 := by
        dsimp [E] at hnext_E hE ⊢
        omega
      have hnext_lt : E next < e := by omega
      have hk_next : k ≤ E next := by omega
      exact ih (E next) hnext_lt next hnext_mem rfl k hk_next
  intro k hk
  exact hmain (E start) start hstart rfl k hk

/-- A top cell plus no-prime unit-holonomy exclusion produces active support
for every possible endpoint-energy gap below the top. -/
theorem noPrimeEndpointActiveSupport_of_noUnitHolonomy_and_topCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ)
    (start : SU7NoPrimeBranchingSpectrumCell C n)
    (hstart : start ∈ xs)
    (htop : noPrimeBranchingEndpointResidualEnergy start = maxEnergy)
    (hforbid : NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs) :
    NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy := by
  have Hsucc : NoPrimeBranchingCellUnitSuccessorLaw xs :=
    (noPrimeNoUnitHolonomy_iff_cellUnitSuccessorLaw xs).mp hforbid
  refine { upper_of_gap := ?_ }
  intro gap
  have hle :
      gap.level + 1 ≤
        noPrimeBranchingEndpointResidualEnergy start := by
    rw [htop]
    exact Nat.succ_le_iff.mpr gap.level_lt
  rcases
      exists_noPrimeCell_at_energy_of_unitSuccessorLaw_from_cell
        Hsucc start hstart (gap.level + 1) hle with
    ⟨upperCell, hmem, henergy⟩
  have hnonzero :
      noPrimeBranchingEndpointResidualEnergy upperCell ≠ 0 := by
    intro hzero
    omega
  exact ⟨upperCell, hmem, hnonzero, henergy⟩

/-- A top cell plus no-prime unit-holonomy exclusion forbids endpoint-energy
coverage gaps. -/
theorem noPrimeForbidsEndpointGap_of_noUnitHolonomy_and_topCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ)
    (start : SU7NoPrimeBranchingSpectrumCell C n)
    (hstart : start ∈ xs)
    (htop : noPrimeBranchingEndpointResidualEnergy start = maxEnergy)
    (hforbid : NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs) :
    NoPrimeBranchingEndpointEnergyShellForbidsGap xs maxEnergy := by
  intro gap
  let A :=
    noPrimeEndpointActiveSupport_of_noUnitHolonomy_and_topCell
      xs maxEnergy start hstart htop hforbid
  let G := endpointGapUpperCell_of_activeSupport A gap
  exact hforbid G.upperCell
    (noPrimeUnitHolonomy_of_endpointGapUpperCell G)

/-- A top cell plus no-prime unit-holonomy exclusion forces the executable
endpoint coverage checker to succeed. -/
theorem noPrimeCoverageCheck_true_of_noUnitHolonomy_and_topCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ)
    (start : SU7NoPrimeBranchingSpectrumCell C n)
    (hstart : start ∈ xs)
    (htop : noPrimeBranchingEndpointResidualEnergy start = maxEnergy)
    (hforbid : NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs) :
    noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true :=
  (noPrimeBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
    xs maxEnergy).mpr
    (noPrimeForbidsEndpointGap_of_noUnitHolonomy_and_topCell
      xs maxEnergy start hstart htop hforbid)

/-! ## Finite no-prime max-cell selection -/

/-- A nonempty no-prime branch-cell list contains a cell attaining the
recursive maximum endpoint residual energy of the list. -/
theorem exists_mem_energy_eq_maxNoPrimeEndpointEnergyOfCells_of_ne_nil
    {C : SU7WeightTensorCoding} {n : ℕ} :
    ∀ xs : List (SU7NoPrimeBranchingSpectrumCell C n),
      xs ≠ [] ->
        ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs ∧
            noPrimeBranchingEndpointResidualEnergy B =
              maxNoPrimeBranchingEndpointResidualEnergyOfCells xs := by
  intro xs
  induction xs with
  | nil =>
      intro hne
      exact False.elim (hne rfl)
  | cons B Bs ih =>
      intro _hne
      by_cases htail : Bs = []
      · subst Bs
        refine ⟨B, ?_, ?_⟩
        · simp
        · simp [maxNoPrimeBranchingEndpointResidualEnergyOfCells]
      · rcases ih htail with ⟨Bmax, hmem, henergy⟩
        by_cases hle :
            maxNoPrimeBranchingEndpointResidualEnergyOfCells Bs ≤
              noPrimeBranchingEndpointResidualEnergy B
        · refine ⟨B, ?_, ?_⟩
          · simp
          · simp [maxNoPrimeBranchingEndpointResidualEnergyOfCells,
              max_eq_left hle]
        · have hright :
              noPrimeBranchingEndpointResidualEnergy B ≤
                maxNoPrimeBranchingEndpointResidualEnergyOfCells Bs := by
            exact Nat.le_of_lt (Nat.lt_of_not_ge hle)
          refine ⟨Bmax, ?_, ?_⟩
          · simp [hmem]
          · simp [maxNoPrimeBranchingEndpointResidualEnergyOfCells,
              max_eq_right hright, henergy]

/-- Nonempty no-prime unit-holonomy exclusion forces coverage at the computed
maximum endpoint energy. -/
theorem noPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (hne : xs ≠ [])
    (hforbid : NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs) :
    noPrimeBranchingEnergyShellCoverageCheck xs
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs) = true := by
  rcases
      exists_mem_energy_eq_maxNoPrimeEndpointEnergyOfCells_of_ne_nil
        xs hne with
    ⟨start, hstart, htop⟩
  exact noPrimeCoverageCheck_true_of_noUnitHolonomy_and_topCell
    xs (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs)
    start hstart htop hforbid

/-! ## Certificate -/

/-- P958 certificate: no-prime top confinement produces endpoint coverage
without storing an active-support field or a coverage receipt. -/
structure SU7NoPrimeTopConfinementCoverageCertificate where
  unit_descent_fills_lower_shells :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
      (_Hsucc : NoPrimeBranchingCellUnitSuccessorLaw xs)
      (start : SU7NoPrimeBranchingSpectrumCell C n),
      start ∈ xs ->
        ∀ k : ℕ,
          k ≤ noPrimeBranchingEndpointResidualEnergy start ->
            ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
              B ∈ xs ∧ noPrimeBranchingEndpointResidualEnergy B = k
  top_no_holonomy_to_active_support :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
      (maxEnergy : ℕ)
      (start : SU7NoPrimeBranchingSpectrumCell C n),
      start ∈ xs ->
        noPrimeBranchingEndpointResidualEnergy start = maxEnergy ->
          NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs ->
            NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy
  top_no_holonomy_to_coverage_check :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
      (maxEnergy : ℕ)
      (start : SU7NoPrimeBranchingSpectrumCell C n),
      start ∈ xs ->
        noPrimeBranchingEndpointResidualEnergy start = maxEnergy ->
          NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs ->
            noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true
  finite_max_attained :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n)),
      xs ≠ [] ->
        ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs ∧
            noPrimeBranchingEndpointResidualEnergy B =
              maxNoPrimeBranchingEndpointResidualEnergyOfCells xs
  nonempty_no_holonomy_to_coverage_check :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n)),
      xs ≠ [] ->
        NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs ->
          noPrimeBranchingEnergyShellCoverageCheck xs
            (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs) = true

/-- Canonical P958 no-prime top-confinement coverage certificate. -/
def su7NoPrimeTopConfinementCoverageCertificate :
    SU7NoPrimeTopConfinementCoverageCertificate where
  unit_descent_fills_lower_shells :=
    exists_noPrimeCell_at_energy_of_unitSuccessorLaw_from_cell
  top_no_holonomy_to_active_support :=
    noPrimeEndpointActiveSupport_of_noUnitHolonomy_and_topCell
  top_no_holonomy_to_coverage_check :=
    noPrimeCoverageCheck_true_of_noUnitHolonomy_and_topCell
  finite_max_attained :=
    exists_mem_energy_eq_maxNoPrimeEndpointEnergyOfCells_of_ne_nil
  nonempty_no_holonomy_to_coverage_check :=
    noPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy


end
end StandardModelConstraint
end SaturationMonoid
