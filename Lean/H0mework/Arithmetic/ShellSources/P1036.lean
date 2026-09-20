import H0mework.Arithmetic.ShellSources.P1035

/-!
# Proposition 1036: checked finite shells are direct tensor producers

P1033 built a normalizer from one checked no-prime finite shell with a start
cell.  P1032 then turns fiberwise normalizers into the tensor-atom lift
producer.

This file exposes the executable interface directly:

```text
for every even fiber:
  finite checked no-prime shell + start cell
    -> residual normalizer
    -> tensor-atom lift producer
```

The input is a finite checked shell object, not a zero-cell store and not a
downstream arithmetic endpoint witness.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-- Every even fiber carries a finite checked no-prime shell with an explicit
start cell.  The start cell is only the nonempty source anchor needed by the
normalizer; it is not required to be a zero cell. -/
def SU7NoPrimeCheckedShellWithStartEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7NoPrimeCheckedShellWithStart C n)

/-- Fiberwise finite checked shells produce P933 no-prime residual
normalizers. -/
theorem noPrimeResidualNormalizers_of_checkedShellWithStartEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeCheckedShellWithStartEveryEvenFiber C) :
    SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C := by
  intro n hn
  exact ⟨noPrimeResidualNormalizer_of_checkedShellWithStart
    (Classical.choice (H n hn))⟩

/-- Fiberwise finite checked shells reach the direct tensor-atom lift
producer. -/
theorem su7TensorAtomLiftProducer_of_checkedShellWithStartEveryEvenFiber
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeCheckedShellWithStartEveryEvenFiber C) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_noPrimeResidualNormalizers
    (noPrimeResidualNormalizers_of_checkedShellWithStartEveryEvenFiber H)

/-! ## Canonical raw-coding specialization -/

/-- The same checked-shell interface specialized to the canonical raw tensor
coding. -/
theorem su7TensorAtomLiftProducer_of_rawCheckedShellWithStartEveryEvenFiber
    (H :
      SU7NoPrimeCheckedShellWithStartEveryEvenFiber rawCodeTensorCoding) :
    SU7TensorAtomLiftProducer rawCodeTensorCoding :=
  su7TensorAtomLiftProducer_of_checkedShellWithStartEveryEvenFiber H

/-! ## Certificate -/

/-- P1036 certificate: finite checked shells with starts are now direct
runtime producer inputs for the tensor-atom lift. -/
structure CheckedShellWithStartTensorProducerCertificate where
  checked_shells_to_normalizers :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeCheckedShellWithStartEveryEvenFiber C ->
        SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C
  checked_shells_to_tensor_lift :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeCheckedShellWithStartEveryEvenFiber C ->
        SU7TensorAtomLiftProducer C
  raw_checked_shells_to_tensor_lift :
    SU7NoPrimeCheckedShellWithStartEveryEvenFiber rawCodeTensorCoding ->
      SU7TensorAtomLiftProducer rawCodeTensorCoding

/-- Canonical P1036 checked-shell producer certificate. -/
def checkedShellWithStartTensorProducerCertificate :
    CheckedShellWithStartTensorProducerCertificate where
  checked_shells_to_normalizers :=
    noPrimeResidualNormalizers_of_checkedShellWithStartEveryEvenFiber
  checked_shells_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_checkedShellWithStartEveryEvenFiber
  raw_checked_shells_to_tensor_lift :=
    su7TensorAtomLiftProducer_of_rawCheckedShellWithStartEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
