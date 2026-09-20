import H0mework.Arithmetic.ShellSources.P963

/-!
# Proposition 964: transparent generated shell coverage produces flow

P963 still accepted the executable Boolean coverage check as an input.  P928
proved that this check is equivalent to a transparent shell-realization theorem
over the explicit generated Boolean-atomic branch cells:

```text
GeneratedRawEnergyCoverage n bound
```

This file uses that transparent theorem as the producer input.  The hard
color-loop throat is now a genuine generated shell coverage law, not a Boolean
receipt.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Transparent generated coverage produces the P962 throat -/

/-- Transparent generated raw shell coverage constructs the generated
flow/quantization certificate. -/
def generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (hcoverage : GeneratedRawEnergyCoverage n bound) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_coverageCheck hbound
    (generatedNoPrimeCoverageCheck_of_generatedRawEnergyCoverage hcoverage)

/-- Transparent generated raw shell coverage eliminates filtered unit
permanent holonomy through the no-prime flow/quantization producer. -/
def filteredNoHolonomy_of_generatedEnergyCoverage_via_flowQuantization
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (hcoverage : GeneratedRawEnergyCoverage n bound) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  filteredNoHolonomy_of_generatedNoPrimeFlowQuantization
    (generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage
      hbound hcoverage)

/-! ## Every-fiber transparent shell coverage -/

/-- Every even fiber carries a generated shell coverage theorem. -/
structure SU7GeneratedRawEnergyCoverageEveryEvenFiber where
  codeBound : ℕ -> ℕ
  codeBound_ge_two : ∀ n : ℕ, 2 ≤ n -> 2 ≤ codeBound n
  energy_coverage :
    ∀ n : ℕ, 2 ≤ n -> GeneratedRawEnergyCoverage n (codeBound n)

/-- Fiberwise transparent shell coverage produces P962 flow/quantization
certificates on every even fiber. -/
theorem generatedFlowQuantizationEveryEvenFiber_of_energyCoverage
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiber) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber := by
  intro n hn
  exact
    ⟨generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage
      (H.codeBound_ge_two n hn)
      (H.energy_coverage n hn)⟩

/-- Fiberwise transparent shell coverage eliminates filtered generated
unit permanent holonomy on every even fiber. -/
theorem filteredNoHolonomyEveryEvenFiber_of_energyCoverage
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiber) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ bound : ℕ,
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound
            (noPrimeBranchingAllowedPredicate
              (generatedNoPrimeBranchingCells n bound))) := by
  intro n hn
  exact
    ⟨H.codeBound n,
      filteredNoHolonomy_of_generatedEnergyCoverage_via_flowQuantization
        (H.codeBound_ge_two n hn)
        (H.energy_coverage n hn)⟩

/-! ## Certificate -/

/-- P964 certificate: transparent generated shell coverage, not a Boolean
coverage receipt, produces the no-prime flow/quantization throat. -/
structure SU7TransparentCoverageToFlowQuantizationProducerCertificate where
  energy_coverage_to_flow_quantization :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        GeneratedRawEnergyCoverage n bound ->
          SU7GeneratedNoPrimeFlowQuantizationCertificate n
  energy_coverage_to_filtered_no_holonomy :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        GeneratedRawEnergyCoverage n bound ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))
  every_fiber_to_flow_quantization :
    SU7GeneratedRawEnergyCoverageEveryEvenFiber ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber
  every_fiber_to_filtered_no_holonomy :
    SU7GeneratedRawEnergyCoverageEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ bound : ℕ,
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P964 transparent-coverage producer certificate. -/
def su7TransparentCoverageToFlowQuantizationProducerCertificate :
    SU7TransparentCoverageToFlowQuantizationProducerCertificate where
  energy_coverage_to_flow_quantization := by
    intro n bound hbound hcoverage
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_energyCoverage
        hbound hcoverage
  energy_coverage_to_filtered_no_holonomy := by
    intro n bound hbound hcoverage
    exact
      filteredNoHolonomy_of_generatedEnergyCoverage_via_flowQuantization
        hbound hcoverage
  every_fiber_to_flow_quantization :=
    generatedFlowQuantizationEveryEvenFiber_of_energyCoverage
  every_fiber_to_filtered_no_holonomy :=
    filteredNoHolonomyEveryEvenFiber_of_energyCoverage


end
end StandardModelConstraint
end SaturationMonoid
