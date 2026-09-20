import H0mework.Arithmetic.ShellSources.P960

/-!
# Proposition 961: generated Lyapunov no-gap produces no-prime confinement

P960 reduced the generated no-prime throat to one physical field:

```text
NoPrimeBranchingCellsForbidUnitPermanentHolonomy
  (generatedNoPrimeBranchingCells n bound)
```

This file unfolds that field into the Lyapunov/no-gap package isolated in
P953:

* no strict permanent holonomy;
* endpoint-energy unit-density.

Together these produce the no-prime unit successor law, hence no-prime unit
permanent-holonomy exclusion, hence filtered generated no-holonomy.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generic Lyapunov/no-gap to no-prime unit confinement -/

/-- Strict Lyapunov no-holonomy plus unit-density forbids no-prime unit
permanent holonomy. -/
theorem noPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (Hstrict : NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs)
    (Hdense : NoPrimeBranchingCellEnergyUnitDensity xs) :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs :=
  (noPrimeNoUnitHolonomy_iff_cellUnitSuccessorLaw xs).mpr
    (noPrimeCellUnitSuccessorLaw_of_noStrictHolonomy_and_unitDensity
      Hstrict Hdense)

/-! ## Generated no-prime specialization -/

/-- On the generated no-prime source list, strict Lyapunov no-holonomy plus
unit-density produces the no-prime unit-holonomy exclusion consumed by P960. -/
theorem generatedNoPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
    {n bound : ℕ}
    (Hstrict :
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy
        (generatedNoPrimeBranchingCells n bound))
    (Hdense :
      NoPrimeBranchingCellEnergyUnitDensity
        (generatedNoPrimeBranchingCells n bound)) :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy
      (generatedNoPrimeBranchingCells n bound) :=
  noPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
    Hstrict Hdense

/-- A generated no-prime Lyapunov/no-gap certificate for one fiber. -/
structure SU7GeneratedNoPrimeLyapunovConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_two : 2 ≤ codeBound
  forbids_strict_permanent_holonomy :
    NoPrimeBranchingCellsForbidStrictPermanentHolonomy
      (generatedNoPrimeBranchingCells n codeBound)
  endpoint_unit_density :
    NoPrimeBranchingCellEnergyUnitDensity
      (generatedNoPrimeBranchingCells n codeBound)

/-- A generated Lyapunov/no-gap certificate produces the P960 unit-confinement
certificate. -/
def generatedNoPrimeUnitConfinementCertificate_of_lyapunov
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    SU7GeneratedNoPrimeUnitConfinementCertificate n where
  codeBound := G.codeBound
  codeBound_ge_two := G.codeBound_ge_two
  forbids_noPrime_unit_holonomy :=
    generatedNoPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
      G.forbids_strict_permanent_holonomy
      G.endpoint_unit_density

/-- A generated Lyapunov/no-gap certificate computes generated no-prime
coverage. -/
def generatedNoPrimeCoverageCheck_of_lyapunovCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    noPrimeBranchingEnergyShellCoverageCheck
        (generatedNoPrimeBranchingCells n G.codeBound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n G.codeBound)) = true :=
  generatedNoPrimeCoverageCheck_of_unitConfinementCertificate
    (generatedNoPrimeUnitConfinementCertificate_of_lyapunov G)

/-- A generated Lyapunov/no-gap certificate eliminates filtered unit permanent
holonomy. -/
def filteredNoHolonomy_of_generatedNoPrimeLyapunovCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n G.codeBound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n G.codeBound))) :=
  filteredNoHolonomy_of_generatedNoPrimeUnitConfinementCertificate
    (generatedNoPrimeUnitConfinementCertificate_of_lyapunov G)

/-! ## Every-fiber form -/

/-- Every even fiber carries a generated Lyapunov/no-gap confinement
certificate. -/
def SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedNoPrimeLyapunovConfinementCertificate n)

/-- Fiberwise generated Lyapunov/no-gap confinement gives filtered generated
no-holonomy on every even fiber. -/
theorem filteredNoHolonomyEveryEvenFiber_of_generatedNoPrimeLyapunov
    (H : SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber) :
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
      filteredNoHolonomy_of_generatedNoPrimeLyapunovCertificate G⟩

/-! ## Certificate -/

/-- P961 certificate: generated no-prime confinement is produced by strict
Lyapunov no-holonomy plus endpoint unit-density. -/
structure SU7GeneratedNoPrimeLyapunovConfinementProducerCertificate where
  strict_density_to_unit_confinement :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs ->
        NoPrimeBranchingCellEnergyUnitDensity xs ->
          NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs
  generated_strict_density_to_unit_confinement :
    ∀ {n bound : ℕ},
      NoPrimeBranchingCellsForbidStrictPermanentHolonomy
          (generatedNoPrimeBranchingCells n bound) ->
        NoPrimeBranchingCellEnergyUnitDensity
          (generatedNoPrimeBranchingCells n bound) ->
            NoPrimeBranchingCellsForbidUnitPermanentHolonomy
              (generatedNoPrimeBranchingCells n bound)
  lyapunov_certificate_to_unit_confinement :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeLyapunovConfinementCertificate n ->
        SU7GeneratedNoPrimeUnitConfinementCertificate n
  lyapunov_certificate_to_filtered_no_holonomy :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (gaugeFilteredRawBranchingSpectrum n G.codeBound
          (noPrimeBranchingAllowedPredicate
            (generatedNoPrimeBranchingCells n G.codeBound)))
  every_fiber_to_filtered_no_holonomy :
    SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ bound : ℕ,
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P961 generated no-prime Lyapunov-confinement certificate. -/
def su7GeneratedNoPrimeLyapunovConfinementProducerCertificate :
    SU7GeneratedNoPrimeLyapunovConfinementProducerCertificate where
  strict_density_to_unit_confinement :=
    noPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
  generated_strict_density_to_unit_confinement :=
    generatedNoPrimeForbidsUnitHolonomy_of_noStrictHolonomy_and_density
  lyapunov_certificate_to_unit_confinement :=
    generatedNoPrimeUnitConfinementCertificate_of_lyapunov
  lyapunov_certificate_to_filtered_no_holonomy :=
    filteredNoHolonomy_of_generatedNoPrimeLyapunovCertificate
  every_fiber_to_filtered_no_holonomy :=
    filteredNoHolonomyEveryEvenFiber_of_generatedNoPrimeLyapunov


end
end StandardModelConstraint
end SaturationMonoid
