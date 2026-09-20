import H0mework.Arithmetic.AtomicCodes.P1031
import H0mework.Arithmetic.ShellSources.P933

/-!
# Proposition 1032: no-prime residual dynamics feeds the tensor-atom producer

P1031 isolated the final cycle/atom throat.  This file drives the physical
producer through an even shorter route: no-prime SU(7) branch dynamics already
produces tensor-irreducible endpoint atoms plus a zero endpoint residual.

The generated color-trace half is supplied by the full-orbit incidence
normalizer from P993/P997.  The endpoint-balance half is supplied by the
zero residual cell computed by no-prime residual transport.  Together they
build the P1016 `SU7TensorAtomLiftProducer` directly.

No endpoint arithmetic object, prime-edge loop, or downstream coverage
statement appears in this file.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Lifting one no-prime zero cell into the tensor-atom throat -/

/-- A no-prime zero branch cell supplies the tensor-atom lift on one fiber.

The generated color cell comes from the full-orbit incidence normalizer; the
two tensor-irreducible atoms come from the no-prime branch cell. -/
def tensorAtomLiftWitnessOfNoPrimeZeroCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (B : SU7NoPrimeBranchingSpectrumCell C n)
    (hzero : noPrimeBranchingResidual B = 0) :
    ∃ generated : SU7GeneratedTerminalColorCell n,
      ∃ left right : SU7TensorIrreducibleAtom C,
        ∃ allowed : SameCarrierGaugeAllowed generated,
          SameCarrierTensorAtomicCellZero
            (sameCarrierTensorAtomicCellOfSU7TensorAtoms
              generated left right allowed) := by
  let generated := fullOrbitIncidenceGeneratedCell n
  let left := B.leftAtom.toTensorIrreducibleAtom
  let right := B.rightAtom.toTensorIrreducibleAtom
  let allowed := fullOrbitIncidenceGeneratedCell_allowed n
  refine ⟨generated, left, right, allowed, ?_⟩
  apply sameCarrierTensorAtomicCellOfSU7TensorAtoms_zero_of_trace_and_balance
  · rw [colorTraceResidual_sameCarrierTensorAtomicCellOfSU7TensorAtoms]
    exact fullOrbitIncidenceGeneratedCell_trace_zero n
  · have hsum :
        atomCode B.leftAtom.toSU7Atom +
            atomCode B.rightAtom.toSU7Atom =
          2 * n :=
      noPrimeBranchingResidual_zero_to_sum B hzero
    simpa [left, right, SU7NoPrimeBranchingAtom.toTensorIrreducibleAtom,
      SU7NoPrimeBranchingAtom.toSU7Atom] using hsum

/-! ## Physical confinement dynamics to tensor-atom producer -/

/-- THEOREM 1: no-prime confinement dynamics feeds the same-carrier
tensor-atom lift producer. -/
theorem su7TensorAtomLiftProducer_of_noPrimeConfinementDynamics
    {C : SU7WeightTensorCoding}
    (D : SU7NoPrimeBranchingConfinementDynamics C) :
    SU7TensorAtomLiftProducer C := by
  intro n hn
  exact
    tensorAtomLiftWitnessOfNoPrimeZeroCell
      (D.zeroCell n hn)
      (D.zeroCell_residual_zero n hn)

/-! ## Residual normalizers to tensor-atom producer -/

/-- THEOREM 2: fiberwise no-prime residual normalizers feed the tensor-atom
lift producer.  This route computes the zero cell by residual transport rather
than storing it in the dynamics object. -/
theorem su7TensorAtomLiftProducer_of_noPrimeResidualNormalizers
    {C : SU7WeightTensorCoding}
    (H : SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C) :
    SU7TensorAtomLiftProducer C := by
  intro n hn
  let N : SU7NoPrimeBranchingResidualNormalizer C n := Classical.choice (H n hn)
  let G : SU7GeneratedNoPrimeZeroBranchCell C n :=
    generatedNoPrimeZeroCell_of_normalizer N
  exact tensorAtomLiftWitnessOfNoPrimeZeroCell G.cell G.residual_zero

/-! ## Certificate -/

/-- P1032 certificate: no-prime residual transport is now connected directly
to the refined tensor-atom producer. -/
structure NoPrimeResidualDynamicsTensorAtomProducerCertificate where
  zero_cell_to_tensor_lift :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (B : SU7NoPrimeBranchingSpectrumCell C n),
      noPrimeBranchingResidual B = 0 ->
        ∃ generated : SU7GeneratedTerminalColorCell n,
          ∃ left right : SU7TensorIrreducibleAtom C,
            ∃ allowed : SameCarrierGaugeAllowed generated,
              SameCarrierTensorAtomicCellZero
                (sameCarrierTensorAtomicCellOfSU7TensorAtoms
                  generated left right allowed)
  confinement_to_lift :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeBranchingConfinementDynamics C ->
        SU7TensorAtomLiftProducer C
  normalizers_to_lift :
    ∀ {C : SU7WeightTensorCoding},
      SU7NoPrimeBranchingResidualNormalizerEveryEvenFiber C ->
        SU7TensorAtomLiftProducer C

def noPrimeResidualDynamicsTensorAtomProducerCertificate :
    NoPrimeResidualDynamicsTensorAtomProducerCertificate where
  zero_cell_to_tensor_lift := tensorAtomLiftWitnessOfNoPrimeZeroCell
  confinement_to_lift := su7TensorAtomLiftProducer_of_noPrimeConfinementDynamics
  normalizers_to_lift := su7TensorAtomLiftProducer_of_noPrimeResidualNormalizers


end StandardModelConstraint
end SaturationMonoid
