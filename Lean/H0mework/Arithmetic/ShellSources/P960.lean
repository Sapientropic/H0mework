import H0mework.Arithmetic.ShellSources.P959

/-!
# Proposition 960: generated no-prime nonemptiness is produced by `(2, 2)`

P959 left two fields on the generated no-prime confinement certificate:

```text
generated no-prime source list nonempty
+ no-prime unit permanent holonomy forbidden
```

This file removes the nonemptiness field.  The same canonical `(2, 2)` witness
used by P946 for the raw generated spectrum lifts through P955 into the
generated no-prime branch-cell list.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generated no-prime nonemptiness -/

/-- The generated no-prime branch-cell list is nonempty for every code bound
at least `2`. -/
theorem generatedNoPrimeBranchingCells_nonempty_of_bound_ge_two
    (n bound : ℕ) (hbound : 2 ≤ bound) :
    generatedNoPrimeBranchingCells n bound ≠ [] := by
  rcases
      noPrimeEndpointEnergyShell_of_generatedRawEnergyShell
        (generatedRawEnergyShell_two_two n bound hbound) with
    ⟨B, hBmem, _henergy⟩
  intro hnil
  rw [hnil] at hBmem
  simp at hBmem

/-! ## Unit-confinement-only generated no-prime certificates -/

/-- A generated no-prime confinement certificate whose only substantive
physical field is no-prime unit permanent-holonomy exclusion.

Nonemptiness is produced from `codeBound_ge_two`, not stored as evidence. -/
structure SU7GeneratedNoPrimeUnitConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_two : 2 ≤ codeBound
  forbids_noPrime_unit_holonomy :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy
      (generatedNoPrimeBranchingCells n codeBound)

/-- A unit-confinement-only no-prime certificate produces the P959 generated
no-prime confinement certificate. -/
def generatedNoPrimeConfinementCertificate_of_unitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeUnitConfinementCertificate n) :
    SU7GeneratedNoPrimeConfinementCertificate n where
  codeBound := G.codeBound
  generated_nonempty :=
    generatedNoPrimeBranchingCells_nonempty_of_bound_ge_two
      n G.codeBound G.codeBound_ge_two
  forbids_noPrime_unit_holonomy :=
    G.forbids_noPrime_unit_holonomy

/-- A unit-confinement-only no-prime certificate computes generated no-prime
coverage. -/
def generatedNoPrimeCoverageCheck_of_unitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeUnitConfinementCertificate n) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n G.codeBound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n G.codeBound)) = true :=
  generatedNoPrimeCoverageCheck_of_confinementCertificate
    (generatedNoPrimeConfinementCertificate_of_unitConfinementCertificate G)

/-- A unit-confinement-only no-prime certificate eliminates filtered unit
permanent holonomy in the generated spectrum. -/
def filteredNoHolonomy_of_generatedNoPrimeUnitConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeUnitConfinementCertificate n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n G.codeBound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n G.codeBound))) :=
  filteredNoHolonomy_of_generatedNoPrimeConfinementCertificate
    (generatedNoPrimeConfinementCertificate_of_unitConfinementCertificate G)

/-! ## Every-fiber form -/

/-- Every even fiber carries a generated no-prime unit-confinement certificate.
-/
def SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedNoPrimeUnitConfinementCertificate n)

/-- Fiberwise generated no-prime unit confinement gives filtered generated
no-holonomy on every even fiber. -/
theorem filteredNoHolonomyEveryEvenFiber_of_generatedNoPrimeUnitConfinement
    (H : SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ bound : ℕ,
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound
            (noPrimeBranchingAllowedPredicate
              (generatedNoPrimeBranchingCells n bound))) := by
  intro n hn
  let G := Classical.choice (H n hn)
  exact
    ⟨G.codeBound,
      filteredNoHolonomy_of_generatedNoPrimeUnitConfinementCertificate G⟩

/-! ## Certificate -/

/-- P960 certificate: generated no-prime nonemptiness is produced by the
canonical `(2, 2)` witness; the remaining field is only no-prime unit
permanent-holonomy exclusion. -/
structure SU7GeneratedNoPrimeUnitConfinementProducerCertificate where
  generated_no_prime_nonempty :
    ∀ n bound : ℕ, 2 ≤ bound ->
      generatedNoPrimeBranchingCells n bound ≠ []
  unit_confinement_to_p959_certificate :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeUnitConfinementCertificate n ->
        SU7GeneratedNoPrimeConfinementCertificate n
  unit_confinement_to_coverage :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeUnitConfinementCertificate n),
        noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n G.codeBound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n G.codeBound)) =
            true
  unit_confinement_to_filtered_no_holonomy :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeUnitConfinementCertificate n),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (gaugeFilteredRawBranchingSpectrum n G.codeBound
          (noPrimeBranchingAllowedPredicate
            (generatedNoPrimeBranchingCells n G.codeBound)))
  every_fiber_to_filtered_no_holonomy :
    SU7GeneratedNoPrimeUnitConfinementEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ bound : ℕ,
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P960 generated no-prime unit-confinement producer certificate. -/
def su7GeneratedNoPrimeUnitConfinementProducerCertificate :
    SU7GeneratedNoPrimeUnitConfinementProducerCertificate where
  generated_no_prime_nonempty :=
    generatedNoPrimeBranchingCells_nonempty_of_bound_ge_two
  unit_confinement_to_p959_certificate :=
    generatedNoPrimeConfinementCertificate_of_unitConfinementCertificate
  unit_confinement_to_coverage := by
    intro n G
    exact generatedNoPrimeCoverageCheck_of_unitConfinementCertificate G
  unit_confinement_to_filtered_no_holonomy :=
    filteredNoHolonomy_of_generatedNoPrimeUnitConfinementCertificate
  every_fiber_to_filtered_no_holonomy :=
    filteredNoHolonomyEveryEvenFiber_of_generatedNoPrimeUnitConfinement


end
end StandardModelConstraint
end SaturationMonoid
