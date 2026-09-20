import H0mework.Arithmetic.ShellSources.P961

/-!
# Proposition 962: residual flow plus quantized bridge produces confinement

P961 reduced the generated color-loop throat to two propositions on the
generated no-prime source list:

```text
strict Lyapunov no-holonomy
+ endpoint-energy unit-density
```

This file lowers those propositions into producer objects:

* a confining residual flow chooses a strictly lower-energy branch cell for
  every active cell;
* a quantized unit bridge turns every strict descent into a one-unit successor.

Together they produce the generated Lyapunov/no-gap certificate consumed by
P961.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generic producer objects -/

/-- A confining residual flow on a no-prime branch-cell list.

For every active cell, the flow returns another in-list cell with strictly lower
endpoint residual energy.  This is the discrete Lyapunov-dissipation object,
not a stored zero cell. -/
structure NoPrimeBranchingConfiningResidualFlow
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) where
  lowerCell :
    ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ xs ->
        noPrimeBranchingEndpointResidualEnergy B ≠ 0 ->
          SU7NoPrimeBranchingSpectrumCell C n
  lower_mem :
    ∀ B hmem hnonzero,
      lowerCell B hmem hnonzero ∈ xs
  lower_energy_lt :
    ∀ B hmem hnonzero,
      noPrimeBranchingEndpointResidualEnergy
          (lowerCell B hmem hnonzero) <
        noPrimeBranchingEndpointResidualEnergy B

/-- A quantized unit bridge on a no-prime branch-cell list.

Whenever the flow can descend strictly, the list also contains a one-unit
predecessor of the upper endpoint-energy level. -/
structure NoPrimeBranchingQuantizedUnitBridge
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) where
  unitStep :
    ∀ B lower : SU7NoPrimeBranchingSpectrumCell C n,
      B ∈ xs ->
        lower ∈ xs ->
          noPrimeBranchingEndpointResidualEnergy lower <
            noPrimeBranchingEndpointResidualEnergy B ->
            SU7NoPrimeBranchingSpectrumCell C n
  unitStep_mem :
    ∀ B lower hBmem hlower_mem hlt,
      unitStep B lower hBmem hlower_mem hlt ∈ xs
  unitStep_energy :
    ∀ B lower hBmem hlower_mem hlt,
      noPrimeBranchingEndpointResidualEnergy
          (unitStep B lower hBmem hlower_mem hlt) + 1 =
        noPrimeBranchingEndpointResidualEnergy B

/-! ## Producer objects imply the P961 propositions -/

/-- A confining residual flow gives strict Lyapunov descent. -/
theorem strictSuccessorLaw_of_confiningResidualFlow
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (F : NoPrimeBranchingConfiningResidualFlow xs) :
    NoPrimeBranchingCellStrictSuccessorLaw xs := by
  intro B hmem hnonzero
  exact
    ⟨F.lowerCell B hmem hnonzero,
      F.lower_mem B hmem hnonzero,
      F.lower_energy_lt B hmem hnonzero⟩

/-- A confining residual flow forbids strict permanent holonomy. -/
theorem forbidsStrictPermanentHolonomy_of_confiningResidualFlow
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (F : NoPrimeBranchingConfiningResidualFlow xs) :
    NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs :=
  (noPrimeNoStrictHolonomy_iff_strictSuccessorLaw xs).mpr
    (strictSuccessorLaw_of_confiningResidualFlow F)

/-- A quantized unit bridge gives endpoint-energy unit-density. -/
theorem energyUnitDensity_of_quantizedUnitBridge
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (Q : NoPrimeBranchingQuantizedUnitBridge xs) :
    NoPrimeBranchingCellEnergyUnitDensity xs := by
  intro B lower hBmem hlower_mem hlt
  exact
    ⟨Q.unitStep B lower hBmem hlower_mem hlt,
      Q.unitStep_mem B lower hBmem hlower_mem hlt,
      Q.unitStep_energy B lower hBmem hlower_mem hlt⟩

/-- Confining residual flow plus quantized unit bridge gives the no-prime
branch-cell unit successor law directly.

This is the source-law form of the P962 producer: flow supplies a strict lower
cell, and the quantized bridge turns that strict descent into an exact
one-unit predecessor. -/
theorem noPrimeCellUnitSuccessorLaw_of_flow_and_quantizedBridge
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (F : NoPrimeBranchingConfiningResidualFlow xs)
    (Q : NoPrimeBranchingQuantizedUnitBridge xs) :
    NoPrimeBranchingCellUnitSuccessorLaw xs :=
  noPrimeCellUnitSuccessorLaw_of_strict_and_unitDensity
    (strictSuccessorLaw_of_confiningResidualFlow F)
    (energyUnitDensity_of_quantizedUnitBridge Q)

/-- Confining residual flow plus quantized unit bridge forbids no-prime unit
permanent holonomy. -/
theorem noPrimeForbidsUnitHolonomy_of_flow_and_quantizedBridge
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (F : NoPrimeBranchingConfiningResidualFlow xs)
    (Q : NoPrimeBranchingQuantizedUnitBridge xs) :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs :=
  (noPrimeNoUnitHolonomy_iff_cellUnitSuccessorLaw xs).mpr
    (noPrimeCellUnitSuccessorLaw_of_flow_and_quantizedBridge F Q)

/-! ## Generated no-prime specialization -/

/-- A generated no-prime residual-flow/quantization certificate. -/
structure SU7GeneratedNoPrimeFlowQuantizationCertificate
    (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_two : 2 ≤ codeBound
  residual_flow :
    NoPrimeBranchingConfiningResidualFlow
      (generatedNoPrimeBranchingCells n codeBound)
  quantized_unit_bridge :
    NoPrimeBranchingQuantizedUnitBridge
      (generatedNoPrimeBranchingCells n codeBound)

/-- The generated flow/quantization certificate produces the generated
no-prime branch-cell unit successor law before any no-holonomy readout. -/
theorem generatedNoPrimeCellUnitSuccessorLaw_of_flowQuantizationCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n) :
    NoPrimeBranchingCellUnitSuccessorLaw
      (generatedNoPrimeBranchingCells n G.codeBound) :=
  noPrimeCellUnitSuccessorLaw_of_flow_and_quantizedBridge
    G.residual_flow G.quantized_unit_bridge

/-- The generated flow/quantization certificate produces P961's Lyapunov
confinement certificate. -/
def generatedNoPrimeLyapunovCertificate_of_flowQuantization
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n) :
    SU7GeneratedNoPrimeLyapunovConfinementCertificate n where
  codeBound := G.codeBound
  codeBound_ge_two := G.codeBound_ge_two
  forbids_strict_permanent_holonomy :=
    forbidsStrictPermanentHolonomy_of_confiningResidualFlow
      G.residual_flow
  endpoint_unit_density :=
    energyUnitDensity_of_quantizedUnitBridge
      G.quantized_unit_bridge

/-- The generated flow/quantization certificate eliminates filtered unit
permanent holonomy. -/
def filteredNoHolonomy_of_generatedNoPrimeFlowQuantization
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n G.codeBound
        (noPrimeBranchingAllowedPredicate
          (generatedNoPrimeBranchingCells n G.codeBound))) :=
  filteredNoHolonomy_of_generatedNoPrimeLyapunovCertificate
    (generatedNoPrimeLyapunovCertificate_of_flowQuantization G)

/-! ## Every-fiber form -/

/-- Every even fiber carries a generated flow/quantization certificate. -/
def SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedNoPrimeFlowQuantizationCertificate n)

/-- Fiberwise generated flow/quantization produces filtered generated
no-holonomy on every even fiber. -/
theorem filteredNoHolonomyEveryEvenFiber_of_generatedFlowQuantization
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber) :
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
      filteredNoHolonomy_of_generatedNoPrimeFlowQuantization G⟩

/-! ## Certificate -/

/-- P962 certificate: residual-flow dissipation plus quantized unit bridge
produce the generated no-prime confinement throat. -/
structure SU7GeneratedNoPrimeFlowQuantizationProducerCertificate where
  flow_to_strict_successor :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingConfiningResidualFlow xs ->
        NoPrimeBranchingCellStrictSuccessorLaw xs
  flow_to_no_strict_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingConfiningResidualFlow xs ->
        NoPrimeBranchingCellsForbidStrictPermanentHolonomy xs
  quantized_bridge_to_unit_density :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingQuantizedUnitBridge xs ->
        NoPrimeBranchingCellEnergyUnitDensity xs
  flow_quantized_to_unit_successor :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingConfiningResidualFlow xs ->
        NoPrimeBranchingQuantizedUnitBridge xs ->
          NoPrimeBranchingCellUnitSuccessorLaw xs
  flow_quantized_to_unit_holonomy_forbidden :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingConfiningResidualFlow xs ->
        NoPrimeBranchingQuantizedUnitBridge xs ->
          NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs
  generated_certificate_to_lyapunov :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeFlowQuantizationCertificate n ->
        SU7GeneratedNoPrimeLyapunovConfinementCertificate n
  generated_certificate_to_unit_successor :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n),
        NoPrimeBranchingCellUnitSuccessorLaw
          (generatedNoPrimeBranchingCells n G.codeBound)
  generated_certificate_to_filtered_no_holonomy :
    ∀ {n : ℕ} (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n),
      SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
        (gaugeFilteredRawBranchingSpectrum n G.codeBound
          (noPrimeBranchingAllowedPredicate
            (generatedNoPrimeBranchingCells n G.codeBound)))
  every_fiber_to_filtered_no_holonomy :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ bound : ℕ,
          SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
            (gaugeFilteredRawBranchingSpectrum n bound
              (noPrimeBranchingAllowedPredicate
                (generatedNoPrimeBranchingCells n bound)))

/-- Canonical P962 generated flow/quantization producer certificate. -/
def su7GeneratedNoPrimeFlowQuantizationProducerCertificate :
    SU7GeneratedNoPrimeFlowQuantizationProducerCertificate where
  flow_to_strict_successor :=
    strictSuccessorLaw_of_confiningResidualFlow
  flow_to_no_strict_holonomy :=
    forbidsStrictPermanentHolonomy_of_confiningResidualFlow
  quantized_bridge_to_unit_density :=
    energyUnitDensity_of_quantizedUnitBridge
  flow_quantized_to_unit_successor :=
    noPrimeCellUnitSuccessorLaw_of_flow_and_quantizedBridge
  flow_quantized_to_unit_holonomy_forbidden :=
    noPrimeForbidsUnitHolonomy_of_flow_and_quantizedBridge
  generated_certificate_to_lyapunov :=
    generatedNoPrimeLyapunovCertificate_of_flowQuantization
  generated_certificate_to_unit_successor :=
    generatedNoPrimeCellUnitSuccessorLaw_of_flowQuantizationCertificate
  generated_certificate_to_filtered_no_holonomy :=
    filteredNoHolonomy_of_generatedNoPrimeFlowQuantization
  every_fiber_to_filtered_no_holonomy :=
    filteredNoHolonomyEveryEvenFiber_of_generatedFlowQuantization


end
end StandardModelConstraint
end SaturationMonoid
