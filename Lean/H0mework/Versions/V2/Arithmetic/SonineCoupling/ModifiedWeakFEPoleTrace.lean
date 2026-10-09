import H0mework.Versions.R2.Arithmetic.SonineCoupling.ConjugateTateGaussianSource
import H0mework.Versions.V2.Arithmetic.SonineSource.ModifiedWeakFEQuarterCarrier

/-!
# Pole trace retained by the modified WeakFE source split

The modified WeakFE unit state splits, in the actual quarter graph carrier,
into its zero-read Gaussian part and a unit-read pole part.  The split uses
the source coefficient and the actual almost-everywhere
`f_modif = Gaussian + low + high` identity.  No zero-read vector is erased.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual
open SourceGeneratedFunctionalGraphCokernel

noncomputable section

def positiveModifiedWeakFEPoleTrace
    (owner : GlobalGermOwner) (z : ℂ) : ClozelPositiveMellinFunction :=
  positiveSourceModifiedUnitDetector owner z -
    sourceModifiedUnitCoefficient z •
      positiveGeneratedClozelGaussianRemainder owner

theorem positiveModifiedWeakFEPoleTrace_logQuarter_ae_explicit
    (owner : GlobalGermOwner) (z : ℂ) :
    positiveMellinLogQuarterTransform
        (positiveModifiedWeakFEPoleTrace owner z) =ᵐ[volume]
      positiveMellinLogQuarterTransform
        (sourceModifiedUnitCoefficient z •
          (positiveClozelLowCorrection + positiveClozelHighCorrection)) := by
  have source :=
    positiveGeneratedRiemannModifiedKernel_logQuarter_ae_sum owner
  filter_upwards [source] with x equality
  rw [positiveModifiedWeakFEPoleTrace, map_sub, map_smul, map_smul, map_add]
  rw [show positiveSourceModifiedUnitDetector owner z =
      sourceModifiedUnitCoefficient z •
        positiveGeneratedRiemannModifiedKernel owner by rfl, map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  change sourceModifiedUnitCoefficient z *
        positiveMellinLogQuarterTransform
          (positiveGeneratedRiemannModifiedKernel owner) x -
      sourceModifiedUnitCoefficient z *
        positiveMellinLogQuarterTransform
          (positiveGeneratedClozelGaussianRemainder owner) x =
    sourceModifiedUnitCoefficient z *
      (positiveMellinLogQuarterTransform positiveClozelLowCorrection x +
        positiveMellinLogQuarterTransform positiveClozelHighCorrection x)
  rw [equality]
  rw [map_add, map_add]
  simp only [Pi.add_apply]
  ring

def selectedScaledGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation) :=
  sourceModifiedUnitCoefficient
      (selectedCoPoissonMuntzParameter observation) •
    selectedGaussianQuarterTest observation nontrivial

def reversalGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation) :=
  let relation := positiveClozelMellinRelation owner
    (reversalCoPoissonMuntzParameter observation)
    (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1
  ⟨relation.1,
    ⟨positiveGeneratedClozelGaussianRemainder_mem_quarterL2 owner,
      relation.2⟩⟩

theorem reversalGaussianQuarterTest_functional_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (reversalCoPoissonMuntzParameter observation)
      (reversalGaussianQuarterTest observation nontrivial) = 0 := by
  unfold reversalGaussianQuarterTest reversalCoPoissonMuntzParameter
  change positiveMellinFunctional
      (coordinateReversal observation.coordinate / 2)
      (restrictPositiveMellin _
        ⟨generatedClozelGaussianRemainderKernel owner,
          (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
            observation nontrivial).1⟩) = 0
  rw [positiveMellinFunctional_restrictPositive]
  exact (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
    observation nontrivial).2

def reversalScaledGaussianQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation) :=
  sourceModifiedUnitCoefficient
      (reversalCoPoissonMuntzParameter observation) •
    reversalGaussianQuarterTest observation nontrivial

def selectedModifiedWeakFEPoleTraceTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation) :=
  selectedSourceModifiedUnitQuarterTest observation nontrivial -
    selectedScaledGaussianQuarterTest observation nontrivial

def reversalModifiedWeakFEPoleTraceTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation) :=
  reversalSourceModifiedUnitQuarterTest observation nontrivial -
    reversalScaledGaussianQuarterTest observation nontrivial

theorem selectedModifiedWeakFEPoleTraceTest_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (selectedCoPoissonMuntzParameter observation)
      (selectedModifiedWeakFEPoleTraceTest observation nontrivial) = 1 := by
  rw [selectedModifiedWeakFEPoleTraceTest,
    selectedScaledGaussianQuarterTest, map_sub, map_smul,
    selectedSourceModifiedUnitQuarterTest_functional_one,
    selectedGaussianQuarterTest_functional_zero, smul_zero, sub_zero]

theorem reversalModifiedWeakFEPoleTraceTest_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (reversalCoPoissonMuntzParameter observation)
      (reversalModifiedWeakFEPoleTraceTest observation nontrivial) = 1 := by
  rw [reversalModifiedWeakFEPoleTraceTest,
    reversalScaledGaussianQuarterTest, map_sub, map_smul,
    reversalSourceModifiedUnitQuarterTest_functional_one,
    reversalGaussianQuarterTest_functional_zero, smul_zero, sub_zero]

theorem selectedModifiedWeakFEPoleTraceTest_logQuarter_ae_explicit
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinLogQuarterTransform
        (selectedModifiedWeakFEPoleTraceTest observation nontrivial).1 =ᵐ[volume]
      positiveMellinLogQuarterTransform
        (sourceModifiedUnitCoefficient
            (selectedCoPoissonMuntzParameter observation) •
          (positiveClozelLowCorrection + positiveClozelHighCorrection)) := by
  change positiveMellinLogQuarterTransform
      (positiveModifiedWeakFEPoleTrace owner
        (selectedCoPoissonMuntzParameter observation)) =ᵐ[volume] _
  exact positiveModifiedWeakFEPoleTrace_logQuarter_ae_explicit owner _

theorem reversalModifiedWeakFEPoleTraceTest_logQuarter_ae_explicit
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinLogQuarterTransform
        (reversalModifiedWeakFEPoleTraceTest observation nontrivial).1 =ᵐ[volume]
      positiveMellinLogQuarterTransform
        (sourceModifiedUnitCoefficient
            (reversalCoPoissonMuntzParameter observation) •
          (positiveClozelLowCorrection + positiveClozelHighCorrection)) := by
  change positiveMellinLogQuarterTransform
      (positiveModifiedWeakFEPoleTrace owner
        (reversalCoPoissonMuntzParameter observation)) =ᵐ[volume] _
  exact positiveModifiedWeakFEPoleTrace_logQuarter_ae_explicit owner _

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
