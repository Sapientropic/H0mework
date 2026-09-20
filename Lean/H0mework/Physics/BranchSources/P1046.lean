import H0mework.Arithmetic.ShellSources.P979

/-!
# Proposition 1046: flow/quantization produces residual normalizers

P1044 isolated the remaining zero-shell producer as:

```text
SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber
  -> same-carrier zero fiber on every active even endpoint
```

This file produces that normalizer object itself from the already named
physical throat of P962:

```text
generated residual flow + quantized unit bridge + bound contains 3
  -> generated residual normalizer
```

No arithmetic projection theorem is used here.  The construction is just the
map-level normal form:

* `normalize` is the generated residual flow off the zero endpoint-energy
  fiber and the identity on zero;
* `unitStep` is the quantized unit bridge;
* `codeBound >= 3` is carried explicitly because P976 needs the generated
  `(2,3)` positive-energy witness.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## One fiber -/

/-- Normalize by using the residual flow off the endpoint-zero fiber, and by
fixing endpoint-zero cells.  Outside the generated source list the map is the
identity; the normalizer laws are only required on the generated list. -/
def normalizeOfGeneratedNoPrimeFlowQuantization
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n) :
    SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n := by
  classical
  exact
    if hmem : B ∈ generatedNoPrimeBranchingCells n G.codeBound then
      if hzero : noPrimeBranchingEndpointResidualEnergy B = 0 then
        B
      else
        G.residual_flow.lowerCell B hmem hzero
    else
      B

/-- The flow/quantization object preserves generated-list membership after
normalization. -/
theorem normalizeOfGeneratedNoPrimeFlowQuantization_mem_preserves
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
    (hmem : B ∈ generatedNoPrimeBranchingCells n G.codeBound) :
    normalizeOfGeneratedNoPrimeFlowQuantization G B ∈
      generatedNoPrimeBranchingCells n G.codeBound := by
  unfold normalizeOfGeneratedNoPrimeFlowQuantization
  classical
  by_cases hzero : noPrimeBranchingEndpointResidualEnergy B = 0
  · rw [dif_pos hmem, dif_pos hzero]
    exact hmem
  · rw [dif_pos hmem, dif_neg hzero]
    exact G.residual_flow.lower_mem B hmem hzero

/-- The generated residual-flow normalizer strictly lowers endpoint energy
away from the zero fiber. -/
theorem normalizeOfGeneratedNoPrimeFlowQuantization_strictly_decreases_nonzero
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
    (hmem : B ∈ generatedNoPrimeBranchingCells n G.codeBound)
    (hnonzero : noPrimeBranchingEndpointResidualEnergy B ≠ 0) :
    noPrimeBranchingEndpointResidualEnergy
        (normalizeOfGeneratedNoPrimeFlowQuantization G B) <
      noPrimeBranchingEndpointResidualEnergy B := by
  unfold normalizeOfGeneratedNoPrimeFlowQuantization
  classical
  rw [dif_pos hmem, dif_neg hnonzero]
  exact G.residual_flow.lower_energy_lt B hmem hnonzero

/-- Endpoint-zero generated cells are fixed by the generated residual-flow
normalizer. -/
theorem normalizeOfGeneratedNoPrimeFlowQuantization_fixed_of_zero
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (B : SU7NoPrimeBranchingSpectrumCell rawCodeTensorCoding n)
    (hmem : B ∈ generatedNoPrimeBranchingCells n G.codeBound)
    (hzero : noPrimeBranchingEndpointResidualEnergy B = 0) :
    normalizeOfGeneratedNoPrimeFlowQuantization G B = B := by
  unfold normalizeOfGeneratedNoPrimeFlowQuantization
  classical
  rw [dif_pos hmem, dif_pos hzero]

/-- A P962 generated flow/quantization certificate, with an explicit
`codeBound >= 3`, is exactly a P979 generated no-prime residual normalizer. -/
def generatedNoPrimeResidualNormalizer_of_flowQuantization
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (hbound_three : 3 ≤ G.codeBound) :
    SU7GeneratedNoPrimeResidualNormalizer n where
  codeBound := G.codeBound
  codeBound_ge_three := hbound_three
  normalize := normalizeOfGeneratedNoPrimeFlowQuantization G
  normalize_mem_preserves :=
    normalizeOfGeneratedNoPrimeFlowQuantization_mem_preserves G
  normalize_strictly_decreases_nonzero :=
    normalizeOfGeneratedNoPrimeFlowQuantization_strictly_decreases_nonzero G
  normalize_fixed_of_zero :=
    normalizeOfGeneratedNoPrimeFlowQuantization_fixed_of_zero G
  unitStep := fun B lower hBmem hlower_mem hlt =>
    G.quantized_unit_bridge.unitStep B lower hBmem hlower_mem hlt
  unitStep_mem := by
    intro B lower hBmem hlower_mem hlt
    exact G.quantized_unit_bridge.unitStep_mem B lower hBmem hlower_mem hlt
  unitStep_energy := by
    intro B lower hBmem hlower_mem hlt
    exact G.quantized_unit_bridge.unitStep_energy B lower hBmem hlower_mem hlt

/-! ## Every even fiber -/

/-- Fiberwise generated flow/quantization, with every chosen bound containing
`3`, produces `SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber` itself. -/
theorem generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiber
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber)
    (Hbound :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) :
    SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber := by
  intro n hn
  let G := Classical.choice (H n hn)
  exact
    ⟨generatedNoPrimeResidualNormalizer_of_flowQuantization
      G (Hbound n hn)⟩

/-! ## Certificate -/

/-- P1046 certificate: the generated flow/quantization producer is now wired
directly into the exact P979/P1044 normalizer target.  The P1044 same-carrier
zero theorem can consume the produced every-fiber normalizer without adding any
new producer assumption. -/
structure GeneratedFlowQuantizationResidualNormalizerProducerCertificate where
  one_fiber :
    ∀ {n : ℕ}
      (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n),
      3 ≤ G.codeBound -> SU7GeneratedNoPrimeResidualNormalizer n
  every_fiber :
    ∀ (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber),
      (∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) ->
        SU7GeneratedNoPrimeResidualNormalizerEveryEvenFiber

/-- Canonical P1046 flow/quantization-to-normalizer certificate. -/
def generatedFlowQuantizationResidualNormalizerProducerCertificate :
    GeneratedFlowQuantizationResidualNormalizerProducerCertificate where
  one_fiber := generatedNoPrimeResidualNormalizer_of_flowQuantization
  every_fiber :=
    generatedNoPrimeResidualNormalizers_of_flowQuantizationEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
