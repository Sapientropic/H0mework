import H0mework.Arithmetic.SonineCoupling.ConjugateTateGaussianSource
import H0mework.Arithmetic.SonineSource.ModifiedWeakFEQuarterCarrier

/-!
# Nonzero conjugate--Tate graph source from the modified WeakFE kernel

The source-generated unit detector now descends through the actual closed
Muentz relation.  Its selected graph class has Riesz coordinate one, so it is
nonzero.  The independently generated reversal source is exactly the
conjugate--Tate image of the selected source, not a compared scalar shadow.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedFunctionalGraphCokernel
open scoped InnerProductSpace

noncomputable section

def selectedSourceModifiedUnitGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedCoPoissonMuntzGraphCokernel observation nontrivial :=
  coPoissonMuntzGraphSourceMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (selectedSourceModifiedUnitQuarterTest observation nontrivial)

def reversalSourceModifiedUnitGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReversalCoPoissonMuntzGraphCokernel observation nontrivial :=
  coPoissonMuntzGraphSourceMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (reversalSourceModifiedUnitQuarterTest observation nontrivial)

theorem selectedSourceModifiedUnitGraphClass_riesz
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ⟪ selectedCoPoissonMuntzRieszVector observation nontrivial,
      selectedSourceModifiedUnitGraphClass observation nontrivial⟫_ℂ = 1 := by
  unfold selectedSourceModifiedUnitGraphClass
  rw [selectedCoPoissonMuntzRieszVector_source_readback]
  exact selectedSourceModifiedUnitQuarterTest_functional_one
    observation nontrivial

theorem reversalSourceModifiedUnitGraphClass_riesz
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ⟪ reversalCoPoissonMuntzRieszVector observation nontrivial,
      reversalSourceModifiedUnitGraphClass observation nontrivial⟫_ℂ = 1 := by
  unfold reversalSourceModifiedUnitGraphClass
  rw [reversalCoPoissonMuntzRieszVector_source_readback]
  exact reversalSourceModifiedUnitQuarterTest_functional_one
    observation nontrivial

theorem selectedSourceModifiedUnitGraphClass_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedSourceModifiedUnitGraphClass observation nontrivial ≠ 0 := by
  intro equality
  have readback := selectedSourceModifiedUnitGraphClass_riesz
    observation nontrivial
  rw [equality, inner_zero_right] at readback
  norm_num at readback

/-- The new unit source is genuinely different from the zero-read Gaussian
source class in the actual graph quotient. -/
theorem selectedSourceModifiedUnitGraphClass_ne_gaussian
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedSourceModifiedUnitGraphClass observation nontrivial ≠
      selectedGaussianGraphClass observation nontrivial := by
  intro equality
  have readback := congrArg
    (fun value : SelectedCoPoissonMuntzGraphCokernel observation nontrivial =>
      ⟪ selectedCoPoissonMuntzRieszVector observation nontrivial, value⟫_ℂ)
    equality
  rw [selectedSourceModifiedUnitGraphClass_riesz] at readback
  unfold selectedGaussianGraphClass at readback
  rw [selectedCoPoissonMuntzRieszVector_source_readback,
    selectedGaussianQuarterTest_functional_zero] at readback
  norm_num at readback

def generatedHighSourceModifiedUnitQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)) :=
  conjugateTateQuarterMellinTest
    (selectedCoPoissonMuntzParameter observation)
    (selectedSourceModifiedUnitQuarterTest observation nontrivial)

/-- Independent reversal face: its convergence and unit read are generated
from the reversal zero of the same owner occurrence. -/
def independentHighSourceModifiedUnitQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)) :=
  ⟨positiveSourceModifiedUnitDetector owner
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation)),
    ⟨positiveSourceModifiedUnitDetector_mem_quarterL2 owner _, by
      rw [gaussian_conjugateTateParameter_eq_reversal observation]
      exact (reversalSourceModifiedUnitQuarterTest
        observation nontrivial).2.2⟩⟩

theorem generatedHighSourceModifiedUnitQuarterTest_eq_independent
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedHighSourceModifiedUnitQuarterTest observation nontrivial =
      independentHighSourceModifiedUnitQuarterTest observation nontrivial := by
  apply Subtype.ext
  unfold generatedHighSourceModifiedUnitQuarterTest
    independentHighSourceModifiedUnitQuarterTest
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (positiveSourceModifiedUnitDetector owner
          (selectedCoPoissonMuntzParameter observation))) =
    positiveSourceModifiedUnitDetector owner
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation))
  rw [positiveSourceModifiedUnitDetector_conjugateTate]

def generatedHighSourceModifiedUnitGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ConjugateTateGeneratedHighGraphCokernel
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial) :=
  coPoissonMuntzGraphSourceMap
    (conjugateTateMellinParameter
      (selectedCoPoissonMuntzParameter observation))
    (conjugateTateMellinParameter_re_pos
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
    (conjugateTateMellinParameter_re_lt_half
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
    (independentHighSourceModifiedUnitQuarterTest observation nontrivial)

theorem conjugateTate_selectedSourceModifiedUnitGraphClass
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    conjugateTateCoPoissonMuntzQuotientIsometricEquiv
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedSourceModifiedUnitGraphClass observation nontrivial) =
      generatedHighSourceModifiedUnitGraphClass observation nontrivial := by
  unfold selectedSourceModifiedUnitGraphClass
    generatedHighSourceModifiedUnitGraphClass
  rw [conjugateTateCoPoissonMuntzQuotientIsometricEquiv_source]
  exact congrArg
    (coPoissonMuntzGraphSourceMap
      (conjugateTateMellinParameter
        (selectedCoPoissonMuntzParameter observation))
      (conjugateTateMellinParameter_re_pos
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
      (conjugateTateMellinParameter_re_lt_half
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)))
    (generatedHighSourceModifiedUnitQuarterTest_eq_independent
      observation nontrivial)

theorem sourceModifiedUnitIdentityEndpointResidual_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedHighSourceModifiedUnitGraphClass observation nontrivial -
      conjugateTateCoPoissonMuntzQuotientIsometricEquiv
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedSourceModifiedUnitGraphClass observation nontrivial) = 0 := by
  rw [conjugateTate_selectedSourceModifiedUnitGraphClass, sub_self]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
