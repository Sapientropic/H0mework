import H0mework.Arithmetic.CodePairs.P952

/-!
# Proposition 953: Lyapunov/no-gap form for no-prime branch-cell lists

P952 showed that no-prime branch-cell unit descent eliminates the filtered
permanent holonomy of P950.  P953 gives the Lyapunov form that a physical
producer should actually supply:

* strict residual-energy descent for every active cell;
* unit-density at the top of every strict descent.

Together they force the one-unit successor law on the source no-prime
branch-cell list.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Strict descent and unit-density on no-prime branch-cell lists -/

/-- Strict Lyapunov descent on a no-prime branch-cell list. -/
def NoPrimeBranchingCellStrictSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
    B ∈ xs ->
      noPrimeBranchingEndpointResidualEnergy B ≠ 0 ->
        ∃ lower : SU7NoPrimeBranchingSpectrumCell C n,
          lower ∈ xs ∧
            noPrimeBranchingEndpointResidualEnergy lower <
              noPrimeBranchingEndpointResidualEnergy B

/-- Unit-density at the top of every strict descent in a no-prime branch-cell
list. -/
def NoPrimeBranchingCellEnergyUnitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B lower : SU7NoPrimeBranchingSpectrumCell C n,
    B ∈ xs ->
      lower ∈ xs ->
        noPrimeBranchingEndpointResidualEnergy lower <
          noPrimeBranchingEndpointResidualEnergy B ->
          ∃ step : SU7NoPrimeBranchingSpectrumCell C n,
            step ∈ xs ∧
              noPrimeBranchingEndpointResidualEnergy step + 1 =
                noPrimeBranchingEndpointResidualEnergy B

/-- Strict Lyapunov descent plus unit-density gives no-prime branch-cell unit
successor. -/
theorem noPrimeCellUnitSuccessorLaw_of_strict_and_unitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (Hstrict : NoPrimeBranchingCellStrictSuccessorLaw xs)
    (Hdense : NoPrimeBranchingCellEnergyUnitDensity xs) :
    NoPrimeBranchingCellUnitSuccessorLaw xs := by
  intro B hmem hnonzero
  rcases Hstrict B hmem hnonzero with ⟨lower, hlower_mem, hlower_lt⟩
  exact Hdense B lower hmem hlower_mem hlower_lt

/-! ## Strict permanent holonomy on no-prime branch-cell lists -/

/-- A no-prime branch cell with nonzero residual and no strictly lower
in-list successor. -/
def NoPrimeBranchingCellStrictPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (B : SU7NoPrimeBranchingSpectrumCell C n) : Prop :=
  B ∈ xs ∧
    noPrimeBranchingEndpointResidualEnergy B ≠ 0 ∧
      ∀ lower : SU7NoPrimeBranchingSpectrumCell C n,
        lower ∈ xs ->
          ¬ noPrimeBranchingEndpointResidualEnergy lower <
            noPrimeBranchingEndpointResidualEnergy B

/-- The no-prime branch-cell list forbids strict permanent holonomy. -/
def NoPrimeBranchingCellsForbidStrictPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
    ¬ NoPrimeBranchingCellStrictPermanentHolonomy xs B

/-- Forbidding strict permanent holonomy is exactly strict Lyapunov descent.
-/
theorem noPrimeNoStrictHolonomy_iff_strictSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) :
    NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs ↔
      NoPrimeBranchingCellStrictSuccessorLaw xs := by
  constructor
  · intro H B hmem hnonzero
    by_contra hnone
    have hterminal :
        ∀ lower : SU7NoPrimeBranchingSpectrumCell C n,
          lower ∈ xs ->
            ¬ noPrimeBranchingEndpointResidualEnergy lower <
              noPrimeBranchingEndpointResidualEnergy B := by
      intro lower hlower_mem hlower_lt
      exact hnone ⟨lower, hlower_mem, hlower_lt⟩
    exact H B ⟨hmem, hnonzero, hterminal⟩
  · intro H B hperm
    rcases hperm with ⟨hmem, hnonzero, hterminal⟩
    rcases H B hmem hnonzero with ⟨lower, hlower_mem, hlower_lt⟩
    exact hterminal lower hlower_mem hlower_lt

/-- Strict no-holonomy plus unit-density gives no-prime branch-cell unit
successor. -/
theorem noPrimeCellUnitSuccessorLaw_of_noStrictHolonomy_and_unitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (Hstrict :
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs)
    (Hdense : NoPrimeBranchingCellEnergyUnitDensity xs) :
    NoPrimeBranchingCellUnitSuccessorLaw xs :=
  noPrimeCellUnitSuccessorLaw_of_strict_and_unitDensity
    ((noPrimeNoStrictHolonomy_iff_strictSuccessorLaw xs).mp Hstrict)
    Hdense

/-- Strict no-holonomy plus unit-density eliminates P950 filtered permanent
holonomy for the generated allowed sector. -/
theorem noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_noStrict_and_density
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (Hstrict :
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs)
    (Hdense : NoPrimeBranchingCellEnergyUnitDensity xs) :
    NoPrimeAllowedSectorForbidsUnitPermanentHolonomy bound xs :=
  noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_cellUnitSuccessorLaw
    hbounded
    (noPrimeCellUnitSuccessorLaw_of_noStrictHolonomy_and_unitDensity
      Hstrict Hdense)

/-- The same Lyapunov/no-gap package forbids unit permanent holonomy in the
filtered generated SU(7) spectrum. -/
theorem gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeNoStrict_and_density
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (Hstrict :
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs)
    (Hdense : NoPrimeBranchingCellEnergyUnitDensity xs) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate xs)) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeCellUnitSuccessorLaw
    hbounded
    (noPrimeCellUnitSuccessorLaw_of_noStrictHolonomy_and_unitDensity
      Hstrict Hdense)

/-! ## Certificate -/

/-- P953 certificate: Lyapunov strict descent plus quantized unit-density is
exactly enough to feed the P952 no-prime unit-descent throat. -/
structure SU7NoPrimeLyapunovNoGapCertificate where
  strict_and_density_to_unit_successor :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellStrictSuccessorLaw xs ->
        NoPrimeBranchingCellEnergyUnitDensity xs ->
          NoPrimeBranchingCellUnitSuccessorLaw xs
  no_strict_holonomy_iff_strict_successor :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n)),
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs ↔
        NoPrimeBranchingCellStrictSuccessorLaw xs
  no_strict_and_density_to_no_filtered_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellsWithinBound bound xs ->
        NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs ->
          NoPrimeBranchingCellEnergyUnitDensity xs ->
            NoPrimeAllowedSectorForbidsUnitPermanentHolonomy bound xs
  no_strict_and_density_to_filtered_spectrum_no_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellsWithinBound bound xs ->
        NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs ->
          NoPrimeBranchingCellEnergyUnitDensity xs ->
            SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
              (gaugeFilteredRawBranchingSpectrum n bound
                (noPrimeBranchingAllowedPredicate xs))

/-- Canonical P953 Lyapunov/no-gap certificate. -/
def su7NoPrimeLyapunovNoGapCertificate :
    SU7NoPrimeLyapunovNoGapCertificate where
  strict_and_density_to_unit_successor :=
    noPrimeCellUnitSuccessorLaw_of_strict_and_unitDensity
  no_strict_holonomy_iff_strict_successor :=
    noPrimeNoStrictHolonomy_iff_strictSuccessorLaw
  no_strict_and_density_to_no_filtered_holonomy :=
    noPrimeAllowedSectorForbidsUnitPermanentHolonomy_of_noStrict_and_density
  no_strict_and_density_to_filtered_spectrum_no_holonomy :=
    gaugeFilteredForbidsUnitPermanentHolonomy_of_noPrimeNoStrict_and_density


end
end StandardModelConstraint
end SaturationMonoid
