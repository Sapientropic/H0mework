import H0mework.Physics.ColorLoops.P978

/-!
# Proposition 979: no-prime residual normalizers produce the color loop

P962 names the constructive throat as a residual flow plus a quantized unit
bridge.  This file lowers that object one more step on the generated no-prime
branch cells: a single total normalizer map, together with a unit selector,
generates the P962 flow/bridge object.

The normalizer stores no zero cell, no prime pair, and no Goldbach witness.
It is a residual-transport map on the generated no-prime spectrum:

```text
normalize B = B  iff  endpoint residual energy of B is zero
nonzero B -> normalize B has lower endpoint energy
```

Together with the quantized unit selector, it feeds P976/P978 and therefore
the global SU(7)-filtered color-loop producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generated no-prime residual normalizers -/

/-- A total normalizer on the generated no-prime branch-cell list for one even
fiber.

The map is total on the no-prime cell type, but its laws are only required on
the generated list.  The bound includes `2` and `3`, so P976 can force the
zero-shell throat once the flow/bridge object is produced. -/
structure SU7GeneratedNoPrimeResidualNormalizer (n : ℕ) where
  codeBound : ℕ
  codeBound_ge_three : 3 ≤ codeBound
  normalize :
    SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n ->
      SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n
  normalize_mem_preserves :
    ∀ B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
      B ∈ generatedNoPrimeBranchingCells n codeBound ->
        normalize B ∈ generatedNoPrimeBranchingCells n codeBound
  normalize_strictly_decreases_nonzero :
    ∀ B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
      B ∈ generatedNoPrimeBranchingCells n codeBound ->
        noPrimeBranchingEndpointResidualEnergy B ≠ 0 ->
          noPrimeBranchingEndpointResidualEnergy (normalize B) <
            noPrimeBranchingEndpointResidualEnergy B
  normalize_fixed_of_zero :
    ∀ B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
      B ∈ generatedNoPrimeBranchingCells n codeBound ->
        noPrimeBranchingEndpointResidualEnergy B = 0 ->
          normalize B = B
  unitStep :
    ∀ B lower : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n,
      B ∈ generatedNoPrimeBranchingCells n codeBound ->
        lower ∈ generatedNoPrimeBranchingCells n codeBound ->
          noPrimeBranchingEndpointResidualEnergy lower <
            noPrimeBranchingEndpointResidualEnergy B ->
            SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n
  unitStep_mem :
    ∀ B lower hBmem hlower_mem hlt,
      unitStep B lower hBmem hlower_mem hlt ∈
        generatedNoPrimeBranchingCells n codeBound
  unitStep_energy :
    ∀ B lower hBmem hlower_mem hlt,
      noPrimeBranchingEndpointResidualEnergy
          (unitStep B lower hBmem hlower_mem hlt) + 1 =
        noPrimeBranchingEndpointResidualEnergy B

/-- A nonzero generated no-prime cell cannot be fixed by the residual
normalizer. -/
theorem generatedNoPrimeNormalizer_not_fixed_of_nonzero
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
    (hmem : B ∈ generatedNoPrimeBranchingCells n N.codeBound)
    (hnonzero : noPrimeBranchingEndpointResidualEnergy B ≠ 0) :
    N.normalize B ≠ B := by
  intro hfixed
  have hlt :
      noPrimeBranchingEndpointResidualEnergy B <
        noPrimeBranchingEndpointResidualEnergy B := by
    simpa [hfixed] using
      N.normalize_strictly_decreases_nonzero B hmem hnonzero
  exact (lt_irrefl _ hlt)

/-- On generated no-prime cells, the normalizer fixed points are exactly the
zero endpoint-energy cells. -/
theorem generatedNoPrimeNormalizer_fixed_iff_zeroEnergy
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
    (hmem : B ∈ generatedNoPrimeBranchingCells n N.codeBound) :
    N.normalize B = B ↔ noPrimeBranchingEndpointResidualEnergy B = 0 := by
  constructor
  · intro hfixed
    by_contra hnonzero
    exact
      generatedNoPrimeNormalizer_not_fixed_of_nonzero
        N B hmem hnonzero hfixed
  · intro hzero
    exact N.normalize_fixed_of_zero B hmem hzero

/-! ## Normalizers generate P962 flow/quantization -/

/-- The normalizer map generates P962's residual-flow object. -/
def confiningResidualFlow_of_generatedNoPrimeNormalizer
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n) :
    NoPrimeBranchingConfiningResidualFlow
      (generatedNoPrimeBranchingCells n N.codeBound) where
  lowerCell := fun B _hmem _hnonzero => N.normalize B
  lower_mem := by
    intro B hmem _hnonzero
    exact N.normalize_mem_preserves B hmem
  lower_energy_lt := by
    intro B hmem hnonzero
    exact N.normalize_strictly_decreases_nonzero B hmem hnonzero

/-- The normalizer's unit selector generates P962's quantized unit bridge. -/
def quantizedUnitBridge_of_generatedNoPrimeNormalizer
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n) :
    NoPrimeBranchingQuantizedUnitBridge
      (generatedNoPrimeBranchingCells n N.codeBound) where
  unitStep := fun B lower hBmem hlower_mem hlt =>
    N.unitStep B lower hBmem hlower_mem hlt
  unitStep_mem := by
    intro B lower hBmem hlower_mem hlt
    exact N.unitStep_mem B lower hBmem hlower_mem hlt
  unitStep_energy := by
    intro B lower hBmem hlower_mem hlt
    exact N.unitStep_energy B lower hBmem hlower_mem hlt

/-- The generated no-prime residual normalizer constructs the P962
flow/quantization certificate. -/
def generatedNoPrimeFlowQuantizationCertificate_of_residualNormalizer
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n where
  codeBound := N.codeBound
  codeBound_ge_two :=
    Nat.le_trans (by norm_num) N.codeBound_ge_three
  residual_flow :=
    confiningResidualFlow_of_generatedNoPrimeNormalizer N
  quantized_unit_bridge :=
    quantizedUnitBridge_of_generatedNoPrimeNormalizer N

/-- A generated no-prime residual normalizer directly produces a bounded
Goldbach pair in its fiber. -/
theorem boundedGoldbachPair_of_generatedNoPrimeResidualNormalizer
    {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n) :
    BoundedGoldbachPair n N.codeBound :=
  boundedGoldbachPair_of_generatedNoPrimeFlowQuantizationCertificate
    (generatedNoPrimeFlowQuantizationCertificate_of_residualNormalizer N)
    N.codeBound_ge_three

/-! ## Every-fiber normalizers project to global color loops -/

/-- Every even fiber carries a generated no-prime residual normalizer. -/
def SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedNoPrimeResidualNormalizer n)

/-- Fiberwise generated no-prime normalizers generate P962 flow/quantization on
every even fiber. -/
theorem generatedFlowQuantizationEveryEven_of_residualNormalizers
    (H : SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber) :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber := by
  intro n hn
  let N := Classical.choice (H n hn)
  exact
    ⟨generatedNoPrimeFlowQuantizationCertificate_of_residualNormalizer N⟩

/-- Fiberwise generated no-prime normalizers give the ordinary even Goldbach
statement. -/
theorem evenGoldbach_of_generatedNoPrimeResidualNormalizers
    (H : SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber) :
    EvenGoldbachStatement := by
  intro n hn
  let N := Classical.choice (H n hn)
  exact
    hasPrimeAdditiveDecomposition_of_boundedGoldbachPair
      (boundedGoldbachPair_of_generatedNoPrimeResidualNormalizer N)

/-- Fiberwise generated no-prime normalizers produce the SU(7)-filtered
prime-edge loop producer. -/
theorem su7FilteredPrimeEdgeLoopProducer_of_generatedNoPrimeResidualNormalizers
    (H : SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber) :
    SU7FilteredPrimeEdgeLoopProducer :=
  (su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach).mpr
    (evenGoldbach_of_generatedNoPrimeResidualNormalizers H)

/-! ## Certificate -/

/-- P979 certificate: generated no-prime normalizers are the map-level producer
for the P962/P976/P978 color-loop throat. -/
structure SU7GeneratedNoPrimeResidualNormalizerProducerCertificate where
  fixed_iff_zero_energy :
    ∀ {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n)
      (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n),
      B ∈ generatedNoPrimeBranchingCells n N.codeBound ->
        (N.normalize B = B ↔
          noPrimeBranchingEndpointResidualEnergy B = 0)
  normalizer_to_flow :
    ∀ {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n),
      NoPrimeBranchingConfiningResidualFlow
        (generatedNoPrimeBranchingCells n N.codeBound)
  normalizer_to_unit_bridge :
    ∀ {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n),
      NoPrimeBranchingQuantizedUnitBridge
        (generatedNoPrimeBranchingCells n N.codeBound)
  normalizer_to_flow_quantization :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeResidualNormalizer n ->
        SU7GeneratedNoPrimeFlowQuantizationCertificate n
  normalizer_to_bounded_pair :
    ∀ {n : ℕ} (N : SU7GeneratedNoPrimeResidualNormalizer n),
      BoundedGoldbachPair n N.codeBound
  every_fiber_to_flow_quantization :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber ->
      SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber
  every_fiber_to_even_goldbach :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber ->
      EvenGoldbachStatement
  every_fiber_to_su7_filtered_loop :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber ->
      SU7FilteredPrimeEdgeLoopProducer

/-- Canonical P979 normalizer producer certificate. -/
def su7GeneratedNoPrimeResidualNormalizerProducerCertificate :
    SU7GeneratedNoPrimeResidualNormalizerProducerCertificate where
  fixed_iff_zero_energy :=
    generatedNoPrimeNormalizer_fixed_iff_zeroEnergy
  normalizer_to_flow :=
    confiningResidualFlow_of_generatedNoPrimeNormalizer
  normalizer_to_unit_bridge :=
    quantizedUnitBridge_of_generatedNoPrimeNormalizer
  normalizer_to_flow_quantization :=
    generatedNoPrimeFlowQuantizationCertificate_of_residualNormalizer
  normalizer_to_bounded_pair :=
    boundedGoldbachPair_of_generatedNoPrimeResidualNormalizer
  every_fiber_to_flow_quantization :=
    generatedFlowQuantizationEveryEven_of_residualNormalizers
  every_fiber_to_even_goldbach :=
    evenGoldbach_of_generatedNoPrimeResidualNormalizers
  every_fiber_to_su7_filtered_loop :=
    su7FilteredPrimeEdgeLoopProducer_of_generatedNoPrimeResidualNormalizers


end
end StandardModelConstraint
end SaturationMonoid
