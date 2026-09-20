import H0mework.Arithmetic.AtomicCodes.P1034
import H0mework.Arithmetic.ShellSources.P966
import H0mework.Arithmetic.ShellSources.P964

/-!
# Proposition 1035: shell coverage reaches the tensor-atom producer

P1034 showed that generated no-prime flow/quantization reaches the direct
`SU7TensorAtomLiftProducer rawCodeTensorCoding` target.

This file moves the producer boundary one step upstream:

```text
transparent raw shell coverage
  -> generated flow/quantization
  -> tensor-atom lift producer

no-prime endpoint shell coverage
  -> generated flow/quantization
  -> tensor-atom lift producer
```

The statements deliberately stay upstream of prime-edge arithmetic: they do
not mention downstream prime-edge endpoint witnesses.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Transparent raw-energy shell coverage -/

/-- Transparent generated raw shell coverage on every even fiber reaches the
same tensor-atom lift producer as P1034. -/
theorem su7TensorAtomLiftProducer_of_generatedRawEnergyCoverageEveryEvenFiber
    (H : SU7GeneratedRawEnergyCoverageEveryEvenFiber) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_generatedFlowQuantizationEveryEvenFiber
    (generatedFlowQuantizationEveryEvenFiber_of_energyCoverage H)

/-! ## No-prime endpoint shell coverage -/

/-- No-prime endpoint shell coverage on every even fiber reaches the same
tensor-atom lift producer.  The branch-cell source list stores SU(7) tensor
atoms and endpoint residual energies, not prime-edge witnesses. -/
theorem su7TensorAtomLiftProducer_of_noPrimeEndpointShellCoverageEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeEndpointShellCoverageEveryEvenFiber C) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_generatedFlowQuantizationEveryEvenFiber
    (generatedFlowQuantizationEveryEvenFiber_of_noPrimeEndpointCoverage H)

/-! ## Pointwise endpoint coverage for the raw coding -/

/-- For the canonical raw tensor coding, fiberwise no-prime endpoint shell
coverage is enough to obtain the direct tensor-atom lift producer. -/
theorem su7TensorAtomLiftProducer_of_rawNoPrimeEndpointShellCoverageEveryEvenFiber
    (H : SU7NoPrimeEndpointShellCoverageEveryEvenFiber rawCodeTensorCoding) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_noPrimeEndpointShellCoverageEveryEvenFiber H

/-! ## Certificate -/

/-- P1035 certificate: both raw shell coverage and no-prime endpoint shell
coverage are now direct upstream producer interfaces for the tensor-atom lift.
-/
structure ShellCoverageTensorAtomProducerCertificate where
  raw_energy_coverage_to_tensor_lift :
    SU7GeneratedRawEnergyCoverageEveryEvenFiber ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding
  endpoint_shell_coverage_to_tensor_lift :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeEndpointShellCoverageEveryEvenFiber C ->
        SU7TensorAtomLiftProducer rawCodeTensorCoding
  raw_endpoint_shell_coverage_to_tensor_lift :
    SU7NoPrimeEndpointShellCoverageEveryEvenFiber rawCodeTensorCoding ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding

/-- Canonical P1035 shell-coverage producer certificate. -/
def shellCoverageTensorAtomProducerCertificate :
    ShellCoverageTensorAtomProducerCertificate where
  raw_energy_coverage_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_generatedRawEnergyCoverageEveryEvenFiber
  endpoint_shell_coverage_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_noPrimeEndpointShellCoverageEveryEvenFiber
  raw_endpoint_shell_coverage_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_rawNoPrimeEndpointShellCoverageEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
