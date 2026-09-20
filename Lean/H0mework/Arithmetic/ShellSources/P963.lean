import H0mework.Arithmetic.CodePairs.P962

/-!
# Proposition 963: checked no-prime coverage constructs flow/quantization

P962 named the constructive throat:

```text
residual flow + quantized unit bridge
```

This file produces those two objects from the executable no-prime energy-shell
coverage rule of P954.  The source objects are still no-prime
`SU7NoPrimeBranchingSpectrumCell`s; prime-edge facts remain projection readouts
from P932/P951.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Turning proposition-level no-gap laws into producer objects -/

/-- A strict successor law constructs a concrete residual-flow object by
choosing one lower-energy branch cell for each active branch cell. -/
def confiningResidualFlow_of_strictSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (H : NoPrimeBranchingCellStrictSuccessorLaw xs) :
    NoPrimeBranchingConfiningResidualFlow xs where
  lowerCell := fun B hmem hnonzero =>
    Classical.choose (H B hmem hnonzero)
  lower_mem := by
    intro B hmem hnonzero
    exact (Classical.choose_spec (H B hmem hnonzero)).1
  lower_energy_lt := by
    intro B hmem hnonzero
    exact (Classical.choose_spec (H B hmem hnonzero)).2

/-- Unit-density constructs a concrete quantized unit bridge by choosing one
unit predecessor for each strict descent top. -/
def quantizedUnitBridge_of_energyUnitDensity
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (H : NoPrimeBranchingCellEnergyUnitDensity xs) :
    NoPrimeBranchingQuantizedUnitBridge xs where
  unitStep := fun B lower hBmem hlower_mem hlt =>
    Classical.choose (H B lower hBmem hlower_mem hlt)
  unitStep_mem := by
    intro B lower hBmem hlower_mem hlt
    exact
      (Classical.choose_spec
        (H B lower hBmem hlower_mem hlt)).1
  unitStep_energy := by
    intro B lower hBmem hlower_mem hlt
    exact
      (Classical.choose_spec
        (H B lower hBmem hlower_mem hlt)).2

/-! ## Checked no-prime rules construct P962 producers -/

/-- A checked no-prime energy-shell rule constructs the residual-flow object. -/
def confiningResidualFlow_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeBranchingConfiningResidualFlow R.cells :=
  confiningResidualFlow_of_strictSuccessorLaw
    (noPrimeCheckedEnergyShell_strictSuccessorLaw R)

/-- A checked no-prime energy-shell rule constructs the quantized unit bridge.
-/
def quantizedUnitBridge_of_checkedEnergyShellRule
    {C : SU7WeightTensorCoding} {n : ℕ}
    (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n) :
    NoPrimeBranchingQuantizedUnitBridge R.cells :=
  quantizedUnitBridge_of_energyUnitDensity
    (noPrimeCheckedEnergyShell_energyUnitDensity R)

/-- A successful generated no-prime coverage check constructs P962's generated
flow/quantization certificate. -/
def generatedNoPrimeFlowQuantizationCertificate_of_coverageCheck
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (hcheck :
      noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n where
  codeBound := bound
  codeBound_ge_two := hbound
  residual_flow :=
    confiningResidualFlow_of_checkedEnergyShellRule
      { cells := generatedNoPrimeBranchingCells n bound
        rawCodeBound := bound
        cells_within_bound := generatedNoPrimeBranchingCellsWithinBound n bound
        coverage_check := hcheck }
  quantized_unit_bridge :=
    quantizedUnitBridge_of_checkedEnergyShellRule
      { cells := generatedNoPrimeBranchingCells n bound
        rawCodeBound := bound
        cells_within_bound := generatedNoPrimeBranchingCellsWithinBound n bound
        coverage_check := hcheck }

/-- A successful raw generated coverage check constructs P962's generated
flow/quantization certificate through the no-prime lift. -/
def generatedNoPrimeFlowQuantizationCertificate_of_rawCoverageCheck
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (hcheck :
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_coverageCheck hbound
    (generatedNoPrimeCoverageCheck_of_generatedRawCoverageCheck hcheck)

/-- Raw generated coverage now produces filtered generated no-holonomy through
the P962 residual-flow/quantization throat, not by storing prime edges. -/
def filteredNoHolonomy_of_rawCoverageCheck_via_flowQuantization
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (hcheck :
      rawBranchingEnergyShellCoverageCheck
          (booleanGeneratedRawBranchingSpectrum n bound)
          (generatedRawBranchingMaxEnergy n bound) = true) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n bound))) :=
  filteredNoHolonomy_of_generatedNoPrimeFlowQuantization
    (generatedNoPrimeFlowQuantizationCertificate_of_rawCoverageCheck
      hbound hcheck)

/-! ## Certificate -/

/-- P963 certificate: executable no-prime energy-shell coverage constructs the
actual residual-flow/quantized-bridge producer objects consumed by P962. -/
structure SU7CheckedCoverageToFlowQuantizationProducerCertificate where
  strict_successor_to_flow :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellStrictSuccessorLaw xs ->
        NoPrimeBranchingConfiningResidualFlow xs
  unit_density_to_bridge :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingCellEnergyUnitDensity xs ->
        NoPrimeBranchingQuantizedUnitBridge xs
  checked_rule_to_flow :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      NoPrimeBranchingConfiningResidualFlow R.cells
  checked_rule_to_bridge :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (R : SU7NoPrimeBranchingCheckedEnergyShellRule C n),
      NoPrimeBranchingQuantizedUnitBridge R.cells
  generated_check_to_flow_quantization :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        noPrimeBranchingEnergyShellCoverageCheck
            (generatedNoPrimeBranchingCells n bound)
            (maxNoPrimeBranchingEndpointResidualEnergyOfCells
              (generatedNoPrimeBranchingCells n bound)) = true ->
          SU7GeneratedNoPrimeFlowQuantizationCertificate n
  raw_check_to_flow_quantization :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        rawBranchingEnergyShellCoverageCheck
            (booleanGeneratedRawBranchingSpectrum n bound)
            (generatedRawBranchingMaxEnergy n bound) = true ->
          SU7GeneratedNoPrimeFlowQuantizationCertificate n
  raw_check_to_filtered_no_holonomy_via_flow :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        rawBranchingEnergyShellCoverageCheck
            (booleanGeneratedRawBranchingSpectrum n bound)
            (generatedRawBranchingMaxEnergy n bound) = true ->
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P963 checked-coverage to flow/quantization certificate. -/
def su7CheckedCoverageToFlowQuantizationProducerCertificate :
    SU7CheckedCoverageToFlowQuantizationProducerCertificate where
  strict_successor_to_flow :=
    confiningResidualFlow_of_strictSuccessorLaw
  unit_density_to_bridge :=
    quantizedUnitBridge_of_energyUnitDensity
  checked_rule_to_flow :=
    confiningResidualFlow_of_checkedEnergyShellRule
  checked_rule_to_bridge :=
    quantizedUnitBridge_of_checkedEnergyShellRule
  generated_check_to_flow_quantization := by
    intro n bound hbound hcheck
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_coverageCheck
        hbound hcheck
  raw_check_to_flow_quantization := by
    intro n bound hbound hcheck
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_rawCoverageCheck
        hbound hcheck
  raw_check_to_filtered_no_holonomy_via_flow := by
    intro n bound hbound hcheck
    exact
      filteredNoHolonomy_of_rawCoverageCheck_via_flowQuantization
        hbound hcheck


end
end StandardModelConstraint
end SaturationMonoid
