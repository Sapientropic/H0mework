import H0mework.Arithmetic.ShellSources.P1033
import H0mework.Arithmetic.CodePairs.P962

/-!
# Proposition 1034: flow quantization reaches the tensor-atom producer

P962 gives the upstream physical throat:

```text
confining residual flow + quantized unit bridge
  -> generated no-prime Lyapunov/no-gap certificate
```

P1033 then turns generated Lyapunov/no-gap into an executable residual
normalizer and finally into `SU7TensorAtomLiftProducer rawCodeTensorCoding`.

This file records the composed producer as a single Lean theorem.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-- Fiberwise generated flow/quantization gives the P1033 generated
Lyapunov/no-gap throat on every even fiber. -/
theorem generatedLyapunovEveryEvenFiber_of_generatedFlowQuantization
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber) :
    SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber := by
  intro n hn
  exact ⟨generatedNoPrimeLyapunovCertificate_of_flowQuantization
    (Classical.choice (H n hn))⟩

/-- Fiberwise generated flow/quantization computes P933 no-prime residual
normalizers on every even fiber. -/
theorem noPrimeResidualNormalizers_of_generatedFlowQuantizationEveryEvenFiber
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber) :
    SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
      rawCodeTensorCoding :=
  noPrimeResidualNormalizers_of_generatedUnitConfinementEveryEvenFiber
    (by
      intro n hn
      exact ⟨generatedNoPrimeUnitConfinementCertificate_of_lyapunov
        (generatedNoPrimeLyapunovCertificate_of_flowQuantization
          (Classical.choice (H n hn)))⟩)

/-- The composed physical producer:

```text
flow dissipation + quantized bridge
  -> Lyapunov/no-gap
  -> checked shell normalizer
  -> tensor-atom lift producer
```
-/
theorem su7TensorAtomLiftProducer_of_generatedFlowQuantizationEveryEvenFiber
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_generatedLyapunovEveryEvenFiber
    (generatedLyapunovEveryEvenFiber_of_generatedFlowQuantization H)

/-- P1034 certificate: generated flow/quantization now reaches the direct
tensor-atom producer without detouring through prime-edge endpoints. -/
structure FlowQuantizationTensorAtomProducerCertificate where
  flow_to_lyapunov :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber ->
      SU7GeneratedNoPrimeLyapunovConfinementEveryEvenFiber
  flow_to_normalizers :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber ->
      SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber
        rawCodeTensorCoding
  flow_to_tensor_lift :
    SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding

/-- Canonical P1034 certificate. -/
def flowQuantizationTensorAtomProducerCertificate :
    FlowQuantizationTensorAtomProducerCertificate where
  flow_to_lyapunov :=
    generatedLyapunovEveryEvenFiber_of_generatedFlowQuantization
  flow_to_normalizers :=
    noPrimeResidualNormalizers_of_generatedFlowQuantizationEveryEvenFiber
  flow_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_generatedFlowQuantizationEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
