import H0mework.Arithmetic.ShellSources.P955

/-!
# Proposition 956: raw generated coverage transports to no-prime coverage

P955 built `generatedNoPrimeBranchingCells` from the explicit Boolean raw
generator.  The remaining executable check should not be duplicated: the raw
generated spectrum already has a finite energy-shell coverage checker.

This file proves that raw generated coverage transports through the no-prime
lift.  The two facts used are structural:

* the no-prime lift preserves endpoint residual energy;
* every generated no-prime cell comes from a generated Boolean raw cell.

Thus the producer throat is one finite raw generated coverage check, not two
parallel receipts.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generic max bound for no-prime endpoint-energy lists -/

/-- If every member of a no-prime branch-cell list has endpoint energy bounded
by `bound`, then the recursive maximum of the list is also bounded by `bound`.
-/
theorem maxNoPrimeBranchingEndpointResidualEnergyOfCells_le_of_mem_bound
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (hbound :
      ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
        B ∈ xs -> noPrimeBranchingEndpointResidualEnergy B ≤ bound) :
    maxNoPrimeBranchingEndpointResidualEnergyOfCells xs ≤ bound := by
  induction xs with
  | nil =>
      simp [maxNoPrimeBranchingEndpointResidualEnergyOfCells]
  | cons B Bs ih =>
      rw [maxNoPrimeBranchingEndpointResidualEnergyOfCells]
      apply max_le
      · exact hbound B (by simp)
      · apply ih
        intro B' hB'
        exact hbound B' (by simp [hB'])

/-! ## Generated no-prime maximum is bounded by raw generated maximum -/

/-- Each generated no-prime branch cell has endpoint energy bounded by the
computed maximum of the underlying generated raw spectrum. -/
theorem generatedNoPrimeEndpointEnergy_le_generatedRawMaxEnergy
    {n bound : ℕ}
    {B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n}
    (hmem : B ∈ generatedNoPrimeBranchingCells n bound) :
    noPrimeBranchingEndpointResidualEnergy B ≤
      generatedRawBranchingMaxEnergy n bound := by
  rcases
      exists_booleanAtomicRawCell_of_mem_generatedNoPrimeBranchingCells
        hmem with
    ⟨x, hxmem, hxB⟩
  subst B
  rw [noPrimeBranchingCellOfBooleanAtomicRawCell_energy_eq]
  exact generatedRawBranching_energy_bound x.cell
    (booleanAtomicCell_mem_booleanGeneratedSpectrum hxmem)

/-- The no-prime generated endpoint-energy maximum is bounded by the raw
generated residual-energy maximum. -/
theorem generatedNoPrimeMaxEnergy_le_generatedRawMaxEnergy
    (n bound : ℕ) :
    maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n bound) ≤
      generatedRawBranchingMaxEnergy n bound :=
  maxNoPrimeBranchingEndpointResidualEnergyOfCells_le_of_mem_bound
    (by
      intro B hmem
      exact generatedNoPrimeEndpointEnergy_le_generatedRawMaxEnergy hmem)

/-! ## Transporting raw generated coverage -/

/-- Raw generated energy coverage transports to the no-prime generated
endpoint-energy Boolean coverage check. -/
theorem generatedNoPrimeCoverageCheck_of_generatedRawEnergyCoverage
    {n bound : ℕ}
    (hcoverage : GeneratedRawEnergyCoverage n bound) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)) = true := by
  unfold noPrimeBranchingEnergyShellCoverageCheck
  apply List.all_eq_true.mpr
  intro k hk
  have hklt_noPrime :
      k <
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound) :=
    List.mem_range.mp hk
  have hklt_raw : k < generatedRawBranchingMaxEnergy n bound :=
    Nat.lt_of_lt_of_le hklt_noPrime
      (generatedNoPrimeMaxEnergy_le_generatedRawMaxEnergy n bound)
  exact generatedNoPrimeHasEndpointEnergy_of_generatedRawEnergyShell
    (hcoverage k hklt_raw)

/-- The existing raw generated Boolean coverage check transports to the
no-prime generated Boolean coverage check. -/
theorem generatedNoPrimeCoverageCheck_of_generatedRawCoverageCheck
    {n bound : ℕ}
    (hcheck :
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)) = true :=
  generatedNoPrimeCoverageCheck_of_generatedRawEnergyCoverage
    ((generatedCoverageCheck_iff_energyCoverage n bound).mp hcheck)

/-- A successful raw generated coverage check is enough to forbid unit
permanent holonomy in the no-prime filtered generated spectrum. -/
theorem generatedRawCoverageCheck_forbidsNoPrimeFilteredSpectrumUnitHolonomy
    {n bound : ℕ}
    (hcheck :
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  generatedNoPrimeCoverageCheck_forbidsFilteredSpectrumUnitHolonomy
    (generatedNoPrimeCoverageCheck_of_generatedRawCoverageCheck hcheck)

/-! ## Certificate -/

/-- P956 certificate: one raw generated coverage check transports through the
no-prime branch-cell lift and feeds the P955/P954/P953 no-gap throat. -/
structure SU7GeneratedRawCoverageToNoPrimeNoGapCertificate where
  no_prime_max_le_raw_max :
    ∀ n bound : ℕ,
      maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound) ≤
        generatedRawBranchingMaxEnergy n bound
  raw_coverage_to_no_prime_check :
    ∀ {n bound : ℕ},
      GeneratedRawEnergyCoverage n bound ->
        noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true
  raw_check_to_no_prime_check :
    ∀ {n bound : ℕ},
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true ->
        noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true
  raw_check_to_filtered_no_holonomy :
    ∀ {n bound : ℕ},
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound
            (noPrimeBranchingAllowedPredicate
              (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P956 raw-to-no-prime no-gap transport certificate. -/
def su7GeneratedRawCoverageToNoPrimeNoGapCertificate :
    SU7GeneratedRawCoverageToNoPrimeNoGapCertificate where
  no_prime_max_le_raw_max :=
    generatedNoPrimeMaxEnergy_le_generatedRawMaxEnergy
  raw_coverage_to_no_prime_check :=
    generatedNoPrimeCoverageCheck_of_generatedRawEnergyCoverage
  raw_check_to_no_prime_check :=
    generatedNoPrimeCoverageCheck_of_generatedRawCoverageCheck
  raw_check_to_filtered_no_holonomy :=
    generatedRawCoverageCheck_forbidsNoPrimeFilteredSpectrumUnitHolonomy


end
end StandardModelConstraint
end SaturationMonoid
