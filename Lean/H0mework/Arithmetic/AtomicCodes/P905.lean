import H0mework.Arithmetic.PrimeShadow.P904
import H0mework.Arithmetic.AtomicCodes.TensorIrreducibilityCore

/-!
# Proposition 905: tensor irreducibility produces atomic SU(7) codes

P904 reduced the prime-code throat to multiplicative atomicity of raw
representation codes.  This file lowers the producer once more: multiplicative
atomicity is forced by a tensor-coding certificate.

The structural input is not `Nat.Prime`.  It is:

* a tensor operation on SU(7) weights;
* code preservation for tensor products;
* a lift saying every numerical factorization of a weight code is represented
  by some tensor decomposition in the carrier;
* irreducibility means no non-unit tensor decomposition.

From those four ingredients, Lean proves tensor irreducibility implies
multiplicative atomicity, hence P904's raw prime-edge projection chain.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Tensor irreducibility implies raw-code atomicity -/

/-- Tensor irreducibility forces multiplicative atomicity of the raw code. -/
theorem natMultiplicativelyAtomic_of_tensorIrreducible
    (C : SU7WeightTensorCoding) {w : SU7WeightLattice}
    (hirr : SU7TensorIrreducible C w) :
    NatMultiplicativelyAtomic w.code := by
  constructor
  · exact hirr.1
  · intro a b hfactor
    rcases C.lift_factorization w a b hfactor with
      ⟨u, v, hu, hv, htensor⟩
    rcases hirr.2 u v htensor with hu1 | hv1
    · left
      simpa [hu] using hu1
    · right
      simpa [hv] using hv1

/-- Tensor irreducibility also gives primality through P904's atomic bridge. -/
theorem primeCode_of_tensorIrreducible
    (C : SU7WeightTensorCoding) {w : SU7WeightLattice}
    (hirr : SU7TensorIrreducible C w) :
    Nat.Prime w.code :=
  Nat.Prime.of_multiplicativelyAtomic
    (natMultiplicativelyAtomic_of_tensorIrreducible C hirr)

/-- Tensor realization gives P904's atomic producer law. -/
theorem SU7IrreducibleCodeAtomicProducerLaw_of_tensorCodingRealization
    (C : SU7WeightTensorCoding)
    (H : SU7TensorCodingRealizesIrreducibility C) :
    SU7IrreducibleCodeAtomicProducerLaw := by
  intro w hirr
  exact natMultiplicativelyAtomic_of_tensorIrreducible C (H w hirr)

/-- Tensor realization gives P878's prime producer throat. -/
theorem SU7IrreducibleCodePrimeProducerLaw_of_tensorCodingRealization
    (C : SU7WeightTensorCoding)
    (H : SU7TensorCodingRealizesIrreducibility C) :
    SU7IrreducibleCodePrimeProducerLaw :=
  SU7IrreducibleCodePrimeProducerLaw_of_atomicProducerLaw
    (SU7IrreducibleCodeAtomicProducerLaw_of_tensorCodingRealization C H)

/-- Tensor realization drives P903's raw branching-decomposition projection. -/
def traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual_tensor
    (C : SU7WeightTensorCoding)
    (H : SU7TensorCodingRealizesIrreducibility C)
    {n : ℕ} (B : SU7BranchingDecompositionCell n)
    (hzero : rawAtomCodeBranchingDecompositionResidual B = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual_atomic
    (SU7IrreducibleCodeAtomicProducerLaw_of_tensorCodingRealization C H)
    B hzero

/-- Tensor realization drives P903's raw physical-cell projection. -/
def traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual_tensor
    (C : SU7WeightTensorCoding)
    (H : SU7TensorCodingRealizesIrreducibility C)
    {n : ℕ} (B : SU7PhysicalBranchingSpectrumCell n)
    (hzero : rawAtomCodePhysicalBranchingSpectrumResidual B = 0) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual_atomic
    (SU7IrreducibleCodeAtomicProducerLaw_of_tensorCodingRealization C H)
    B hzero

/-! ## Certificate -/

/-- P905 certificate: a tensor-coding realization of SU(7) irreducibility
produces the atomic and prime raw-code projection chain. -/
structure SU7TensorIrreducibilityProducerCertificate where
  raw_tensor_coding : SU7WeightTensorCoding
  tensor_irreducible_to_atomic :
    ∀ (C : SU7WeightTensorCoding) (w : SU7WeightLattice),
      SU7TensorIrreducible C w ->
        NatMultiplicativelyAtomic w.code
  tensor_irreducible_to_prime :
    ∀ (C : SU7WeightTensorCoding) (w : SU7WeightLattice),
      SU7TensorIrreducible C w ->
        Nat.Prime w.code
  tensor_realization_to_atomic_producer :
    ∀ (C : SU7WeightTensorCoding),
      SU7TensorCodingRealizesIrreducibility C ->
        SU7IrreducibleCodeAtomicProducerLaw
  tensor_realization_to_prime_producer :
    ∀ (C : SU7WeightTensorCoding),
      SU7TensorCodingRealizesIrreducibility C ->
        SU7IrreducibleCodePrimeProducerLaw
  tensor_realization_raw_decomposition_to_trace_zero :
    ∀ (C : SU7WeightTensorCoding)
      (_H : SU7TensorCodingRealizesIrreducibility C)
      {n : ℕ} (B : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidual B = 0 ->
        TraceZeroPrimeEdgeLoop n
  tensor_realization_raw_physical_to_trace_zero :
    ∀ (C : SU7WeightTensorCoding)
      (_H : SU7TensorCodingRealizesIrreducibility C)
      {n : ℕ} (B : SU7PhysicalBranchingSpectrumCell n),
      rawAtomCodePhysicalBranchingSpectrumResidual B = 0 ->
        TraceZeroPrimeEdgeLoop n

def su7TensorIrreducibilityProducerCertificate :
    SU7TensorIrreducibilityProducerCertificate where
  raw_tensor_coding := rawCodeTensorCoding
  tensor_irreducible_to_atomic := by
    intro C w hirr
    exact natMultiplicativelyAtomic_of_tensorIrreducible C hirr
  tensor_irreducible_to_prime := by
    intro C w hirr
    exact primeCode_of_tensorIrreducible C hirr
  tensor_realization_to_atomic_producer :=
    SU7IrreducibleCodeAtomicProducerLaw_of_tensorCodingRealization
  tensor_realization_to_prime_producer :=
    SU7IrreducibleCodePrimeProducerLaw_of_tensorCodingRealization
  tensor_realization_raw_decomposition_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawBranchingDecompositionResidual_tensor
  tensor_realization_raw_physical_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawPhysicalBranchingSpectrumResidual_tensor


end
end StandardModelConstraint
end SaturationMonoid
