import H0mework.Arithmetic.ShellSources.P958

/-!
# Proposition 959: generated no-prime confinement produces filtered no-holonomy

P958 proved the generic no-prime source-list theorem:

```text
nonempty source list
+ unit permanent holonomy forbidden
-> endpoint coverage check
```

This file specializes that theorem to the real generated no-prime branch-cell
list from P955.  The source list is still produced from the Boolean raw SU(7)
generator and stores no `Nat.Prime` proofs, no trace-zero loop, and no coverage
receipt.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generated no-prime confinement -/

/-- Generated no-prime unit-holonomy exclusion forces the generated no-prime
endpoint coverage checker to succeed. -/
theorem generatedNoPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
    {n bound : ℕ}
    (hne : generatedNoPrimeBranchingCells n bound ≠ [])
    (hforbid :
      NoPrimeBranchingCellsForbidUnitPermanentHolonomy
        (generatedNoPrimeBranchingCells n bound)) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)) = true :=
  noPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
    (generatedNoPrimeBranchingCells n bound) hne hforbid

/-- Generated no-prime unit-holonomy exclusion eliminates unit permanent
holonomy in the corresponding filtered generated SU(7) raw spectrum. -/
theorem generatedNoPrimeNonemptyNoUnitHolonomy_forbidsFilteredSpectrumUnitHolonomy
    {n bound : ℕ}
    (hne : generatedNoPrimeBranchingCells n bound ≠ [])
    (hforbid :
      NoPrimeBranchingCellsForbidUnitPermanentHolonomy
        (generatedNoPrimeBranchingCells n bound)) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  generatedNoPrimeCoverageCheck_forbidsFilteredSpectrumUnitHolonomy
    (generatedNoPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
      hne hforbid)

/-! ## Certificate object -/

/-- A generated no-prime confinement certificate for one even fiber.

It stores only the generated-list nonemptiness and the physical no-unit-holonomy
law.  Coverage is computed by P958, and filtered no-holonomy follows through
P955/P954.
-/
structure SU7GeneratedNoPrimeConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  generated_nonempty :
    generatedNoPrimeBranchingCells n codeBound ≠ []
  forbids_noPrime_unit_holonomy :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy
      (generatedNoPrimeBranchingCells n codeBound)

/-- The generated no-prime confinement certificate computes the endpoint
coverage checker. -/
def generatedNoPrimeCoverageCheck_of_confinementCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeConfinementCertificate n) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n G.codeBound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n G.codeBound)) = true :=
  generatedNoPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
    G.generated_nonempty
    G.forbids_noPrime_unit_holonomy

/-- The generated no-prime confinement certificate eliminates filtered unit
permanent holonomy. -/
def filteredNoHolonomy_of_generatedNoPrimeConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeConfinementCertificate n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n G.codeBound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n G.codeBound))) :=
  generatedNoPrimeNonemptyNoUnitHolonomy_forbidsFilteredSpectrumUnitHolonomy
    G.generated_nonempty
    G.forbids_noPrime_unit_holonomy

/-- P959 certificate: generated no-prime nonemptiness plus no-unit-holonomy
confinement produces filtered no-holonomy. -/
structure SU7GeneratedNoPrimeConfinementProducerCertificate where
  generated_nonempty_no_unit_to_coverage :
    ∀ {n bound : ℕ},
      generatedNoPrimeBranchingCells n bound ≠ [] ->
        NoPrimeBranchingCellsForbidUnitPermanentHolonomy
          (generatedNoPrimeBranchingCells n bound) ->
          noPrimeBranchingEnergyShellCoverageCheck
            (generatedNoPrimeBranchingCells n bound)
            (maxNoPrimeBranchingEndpointResidualEnergyOfCells
              (generatedNoPrimeBranchingCells n bound)) = true
  generated_nonempty_no_unit_to_filtered_no_holonomy :
    ∀ {n bound : ℕ},
      generatedNoPrimeBranchingCells n bound ≠ [] ->
        NoPrimeBranchingCellsForbidUnitPermanentHolonomy
          (generatedNoPrimeBranchingCells n bound) ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))
  certificate_to_coverage :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeConfinementCertificate n),
      noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n G.codeBound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n G.codeBound)) = true

/-- Canonical P959 generated no-prime confinement producer certificate.

The last field is intentionally kept out of this compact certificate because
Lean's anonymous-field projection notation would make the structure noisy; the
two theorem fields above are the stable API.
-/
def su7GeneratedNoPrimeConfinementProducerCertificate :
    SU7GeneratedNoPrimeConfinementProducerCertificate where
  generated_nonempty_no_unit_to_coverage :=
    generatedNoPrimeCoverageCheck_true_of_nonempty_noUnitHolonomy
  generated_nonempty_no_unit_to_filtered_no_holonomy :=
    generatedNoPrimeNonemptyNoUnitHolonomy_forbidsFilteredSpectrumUnitHolonomy
  certificate_to_coverage := by
    intro n G
    exact generatedNoPrimeCoverageCheck_of_confinementCertificate G


end
end StandardModelConstraint
end SaturationMonoid
