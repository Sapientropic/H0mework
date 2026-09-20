import H0mework.Arithmetic.ShellSources.P953

/-!
# Proposition 954: checked energy-shell producer for no-prime branch cells

P953 isolated the physical no-gap obligations on a no-prime SU(7)
branch-cell list:

* strict Lyapunov descent;
* unit-density of endpoint residual-energy shells.

This file makes that throat executable for the no-prime list itself.  The
checker scans only the residual-energy levels of the generated branch cells.
The cells still store no `Nat.Prime`, no prime pair, and no zero-cell witness.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Computed endpoint-energy bounds -/

/-- Recursive maximum endpoint residual energy of a no-prime branch-cell list.
-/
def maxNoPrimeBranchingEndpointResidualEnergyOfCells
    {C : SU7WeightTensorCoding} {n : ℕ} :
    List (SU7NoPrimeBranchingSpectrumCell C n) -> ℕ
  | [] => 0
  | B :: Bs =>
      max (noPrimeBranchingEndpointResidualEnergy B)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells Bs)

/-- Every no-prime branch cell in a finite list is bounded by the recursive
maximum endpoint residual energy. -/
theorem noPrimeBranchingEndpointEnergy_le_maxOfCells
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {B : SU7NoPrimeBranchingSpectrumCell C n}
    (hmem : B ∈ xs) :
    noPrimeBranchingEndpointResidualEnergy B ≤
      maxNoPrimeBranchingEndpointResidualEnergyOfCells xs := by
  induction xs with
  | nil =>
      simp at hmem
  | cons x xs ih =>
      rw [List.mem_cons] at hmem
      rw [maxNoPrimeBranchingEndpointResidualEnergyOfCells]
      rcases hmem with hB | htail
      · subst B
        exact Nat.le_max_left
          (noPrimeBranchingEndpointResidualEnergy x)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs)
      · exact Nat.le_trans (ih htail)
          (Nat.le_max_right
            (noPrimeBranchingEndpointResidualEnergy x)
            (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs))

/-! ## Boolean endpoint-energy coverage checker -/

/-- Boolean membership test: does the no-prime branch-cell list contain a
cell with endpoint residual energy `k`? -/
def noPrimeBranchingCellHasEndpointEnergy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (k : ℕ) : Bool :=
  xs.any
    (fun B => decide (noPrimeBranchingEndpointResidualEnergy B = k))

/-- A successful endpoint-energy membership check produces an actual
no-prime branch cell from the source list. -/
theorem exists_noPrimeBranchingCell_of_hasEndpointEnergy_eq_true
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (k : ℕ)
    (h : noPrimeBranchingCellHasEndpointEnergy xs k = true) :
    ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ xs ∧ noPrimeBranchingEndpointResidualEnergy B = k := by
  unfold noPrimeBranchingCellHasEndpointEnergy at h
  rcases List.any_eq_true.mp h with ⟨B, hmem, henergy⟩
  exact ⟨B, hmem, decide_eq_true_eq.mp henergy⟩

/-- Endpoint energy-shell coverage for a no-prime branch-cell list.

For every positive endpoint residual-energy level within the finite bound, the
source list contains a branch cell in the adjacent predecessor shell. -/
def NoPrimeBranchingEndpointEnergyShellCoverage
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) : Prop :=
  ∀ e : ℕ, 0 < e -> e ≤ maxEnergy ->
    ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ xs ∧ noPrimeBranchingEndpointResidualEnergy B = e - 1

/-- Boolean coverage check for all adjacent predecessor endpoint-energy
levels below the finite bound. -/
def noPrimeBranchingEnergyShellCoverageCheck
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) : Bool :=
  (List.range maxEnergy).all
    (fun k => noPrimeBranchingCellHasEndpointEnergy xs k)

/-- A successful Boolean endpoint-energy coverage check proves the transparent
coverage proposition. -/
theorem noPrimeBranchingEndpointEnergyShellCoverage_of_check
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ)
    (hcheck : noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true) :
    NoPrimeBranchingEndpointEnergyShellCoverage xs maxEnergy := by
  intro e hpos hle
  have hk : e - 1 < maxEnergy := by omega
  have hhas :
      noPrimeBranchingCellHasEndpointEnergy xs (e - 1) = true :=
    (List.all_eq_true.mp hcheck) (e - 1) (List.mem_range.mpr hk)
  exact exists_noPrimeBranchingCell_of_hasEndpointEnergy_eq_true
    xs (e - 1) hhas

/-! ## Checked no-prime branch-cell producer -/

/-- A checked no-prime branch-cell list.

The raw endpoint-code bound is still explicit because it is the bound required
by P952 when the source list is projected into the filtered generated raw
spectrum.  The residual-energy bound is computed from the source list itself.
-/
structure SU7NoPrimeBranchingCheckedEnergyShellRule
    (C : SU7WeightTensorCoding) (n : ℕ) where
  cells : List (SU7NoPrimeBranchingSpectrumCell C n)
  rawCodeBound : ℕ
  cells_within_bound :
    NoPrimeBranchingCellsWithinBound rawCodeBound cells
  coverage_check :
    noPrimeBranchingEnergyShellCoverageCheck cells
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells cells) = true

/-- A checked no-prime branch-cell list has strict Lyapunov descent. -/
theorem noPrimeCheckedEnergyShell_strictSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeBranchingCellStrictSuccessorLaw R.cells := by
  intro B hmem hnonzero
  let e := noPrimeBranchingEndpointResidualEnergy B
  have hpos : 0 < e := by
    dsimp [e]
    omega
  have hle :
      e ≤ maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells := by
    dsimp [e]
    exact noPrimeBranchingEndpointEnergy_le_maxOfCells hmem
  have hcov :
      NoPrimeBranchingEndpointEnergyShellCoverage R.cells
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells) :=
    noPrimeBranchingEndpointEnergyShellCoverage_of_check
      R.cells
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells)
      R.coverage_check
  rcases hcov e hpos hle with ⟨lower, hlower_mem, hlower_E⟩
  refine ⟨lower, hlower_mem, ?_⟩
  rw [hlower_E]
  omega

/-- A checked no-prime branch-cell list has unit-density at every strict
descent top. -/
theorem noPrimeCheckedEnergyShell_energyUnitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeBranchingCellEnergyUnitDensity R.cells := by
  intro B lower hBmem _hlower_mem hlower_lt
  let e := noPrimeBranchingEndpointResidualEnergy B
  have hpos : 0 < e := by
    dsimp [e]
    omega
  have hle :
      e ≤ maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells := by
    dsimp [e]
    exact noPrimeBranchingEndpointEnergy_le_maxOfCells hBmem
  have hcov :
      NoPrimeBranchingEndpointEnergyShellCoverage R.cells
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells) :=
    noPrimeBranchingEndpointEnergyShellCoverage_of_check
      R.cells
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells R.cells)
      R.coverage_check
  rcases hcov e hpos hle with ⟨step, hstep_mem, hstep_E⟩
  refine ⟨step, hstep_mem, ?_⟩
  rw [hstep_E]
  omega

/-- A checked no-prime branch-cell list forbids strict permanent holonomy. -/
theorem noPrimeCheckedEnergyShell_forbidsStrictPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeBranchingCellsForbidStrictPermanentHolonomy R.cells :=
  (noPrimeNoStrictHolonomy_iff_strictSuccessorLaw R.cells).mpr
    (noPrimeCheckedEnergyShell_strictSuccessorLaw R)

/-- A checked no-prime branch-cell list feeds P953 and forbids unit permanent
holonomy in the generated allowed sector. -/
theorem noPrimeCheckedEnergyShell_forbidsAllowedUnitHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeAllowedSectorForbidsUnitPermanentHolonomy
      R.rawCodeBound R.cells :=
  noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_noStrict_and_density
    R.cells_within_bound
    (noPrimeCheckedEnergyShell_forbidsStrictPermanentHolonomy R)
    (noPrimeCheckedEnergyShell_energyUnitDensity R)

/-- The same checked source list forbids unit permanent holonomy in the
filtered generated SU(7) raw spectrum. -/
theorem noPrimeCheckedEnergyShell_forbidsFilteredSpectrumUnitHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n R.rawCodeBound
        (noPrimeBranchingAllowedPredicate R.cells)) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeNoStrict_and_density
    R.cells_within_bound
    (noPrimeCheckedEnergyShell_forbidsStrictPermanentHolonomy R)
    (noPrimeCheckedEnergyShell_energyUnitDensity R)

/-! ## Certificate -/

/-- P954 certificate: a finite Boolean endpoint-energy checker on the
no-prime branch-cell source list produces the Lyapunov/no-gap data required by
P953. -/
structure SU7NoPrimeCheckedEnergyShellProducerCertificate where
  has_energy_to_exists_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) (k : ℕ),
      noPrimeBranchingCellHasEndpointEnergy xs k = true ->
        ∃ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs ∧ noPrimeBranchingEndpointResidualEnergy B = k
  coverage_check_to_coverage :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
      (maxEnergy : ℕ),
      noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true ->
        NoPrimeBranchingEndpointEnergyShellCoverage xs maxEnergy
  checked_to_strict_descent :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      NoPrimeBranchingCellStrictSuccessorLaw R.cells
  checked_to_unit_density :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      NoPrimeBranchingCellEnergyUnitDensity R.cells
  checked_to_no_allowed_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      NoPrimeAllowedSectorForbidsUnitPermanentHolonomy
        R.rawCodeBound R.cells
  checked_to_no_filtered_spectrum_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (gaugeFilteredRawBranchingSpectrum n R.rawCodeBound
          (noPrimeBranchingAllowedPredicate R.cells))

/-- Canonical P954 checked no-prime energy-shell producer certificate. -/
def su7NoPrimeCheckedEnergyShellProducerCertificate :
    SU7NoPrimeCheckedEnergyShellProducerCertificate where
  has_energy_to_exists_cell :=
    exists_noPrimeBranchingCell_of_hasEndpointEnergy_eq_true
  coverage_check_to_coverage :=
    noPrimeBranchingEndpointEnergyShellCoverage_of_check
  checked_to_strict_descent := by
    intro C n R
    exact noPrimeCheckedEnergyShell_strictSuccessorLaw R
  checked_to_unit_density :=
    noPrimeCheckedEnergyShell_energyUnitDensity
  checked_to_no_allowed_holonomy :=
    noPrimeCheckedEnergyShell_forbidsAllowedUnitHolonomy
  checked_to_no_filtered_spectrum_holonomy :=
    noPrimeCheckedEnergyShell_forbidsFilteredSpectrumUnitHolonomy


end
end StandardModelConstraint
end SaturationMonoid
