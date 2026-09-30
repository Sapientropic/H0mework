import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphKernelCompatibility
import H0mework.Versions.Y.Arithmetic.SonineGap.ZeroRawDilationAdjointEigenlaw

/-!
# Canonical-source action of the integral orbit

The actual integral dilation orbit is sent through the existing canonical
Müntz graph-cokernel source map.  Integral left translation then commutes
strictly with the already installed raw quotient dilation on the whole
integral carrier.  No new action, root or spectral premise is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open Character.GlobalCoPoissonCurrent
open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedHilbertCokernel
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def selectedCanonicalSourceIntegralOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ]
      CoPoissonMuntzGraphCokernel
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial) :=
  (coPoissonMuntzGraphSourceMap
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    |>.restrictScalars ℤ).comp
      (selectedIntegralDilationTestOrbit observation nontrivial)

def reversalCanonicalSourceIntegralOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ]
      CoPoissonMuntzGraphCokernel
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial) :=
  (coPoissonMuntzGraphSourceMap
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
      (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    |>.restrictScalars ℤ).comp
      (reversalIntegralDilationTestOrbit observation nontrivial)

/-- Selected integral action and raw quotient dilation are the same action in
two dependent faces. -/
theorem selectedCanonicalSourceIntegralOrbit_action_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (rawCoPoissonMuntzGraphCokernelDilationAction
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (scaleSquare scale) (scaleSquare_pos scale)
      |>.toLinearMap.restrictScalars ℤ).comp
        (selectedCanonicalSourceIntegralOrbit observation nontrivial) =
      (selectedCanonicalSourceIntegralOrbit observation nontrivial).comp
        (leftTranslation scale).toLinearMap := by
  apply canonicalBasis.ext
  intro right
  have translated :
      (leftTranslation scale).toLinearMap (delta right) =
        delta (scale * right) :=
    leftTranslation_delta scale right
  rw [canonicalBasis_apply]
  change
    rawCoPoissonMuntzGraphCokernelDilationAction
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (scaleSquare scale) (scaleSquare_pos scale)
        (coPoissonMuntzGraphSourceMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (selectedIntegralDilationTestOrbit observation nontrivial
            (delta right))) =
      coPoissonMuntzGraphSourceMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedIntegralDilationTestOrbit observation nontrivial
          ((leftTranslation scale).toLinearMap (delta right)))
  rw [selectedIntegralDilationTestOrbit_delta,
    translated, selectedIntegralDilationTestOrbit_delta,
    rawCoPoissonMuntzGraphCokernelDilationAction_source]
  apply congrArg (coPoissonMuntzGraphSourceMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
  have composition := LinearMap.congr_fun
    (quarterDilationTestAction_comp
      (selectedCoPoissonMuntzParameter observation)
      (scaleSquare scale) (scaleSquare right)
      (scaleSquare_pos scale) (scaleSquare_pos right))
    (normalizedCoPoissonMuntzQuarterShellTest
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
  simpa only [LinearMap.comp_apply, scaleSquare_mul] using composition

/-- Reversal integral action and raw quotient dilation obey the identical
source-generated square. -/
theorem reversalCanonicalSourceIntegralOrbit_action_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (rawCoPoissonMuntzGraphCokernelDilationAction
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (scaleSquare scale) (scaleSquare_pos scale)
      |>.toLinearMap.restrictScalars ℤ).comp
        (reversalCanonicalSourceIntegralOrbit observation nontrivial) =
      (reversalCanonicalSourceIntegralOrbit observation nontrivial).comp
        (leftTranslation scale).toLinearMap := by
  apply canonicalBasis.ext
  intro right
  have translated :
      (leftTranslation scale).toLinearMap (delta right) =
        delta (scale * right) :=
    leftTranslation_delta scale right
  rw [canonicalBasis_apply]
  change
    rawCoPoissonMuntzGraphCokernelDilationAction
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (scaleSquare scale) (scaleSquare_pos scale)
        (coPoissonMuntzGraphSourceMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (reversalIntegralDilationTestOrbit observation nontrivial
            (delta right))) =
      coPoissonMuntzGraphSourceMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (reversalIntegralDilationTestOrbit observation nontrivial
          ((leftTranslation scale).toLinearMap (delta right)))
  rw [reversalIntegralDilationTestOrbit_delta,
    translated, reversalIntegralDilationTestOrbit_delta,
    rawCoPoissonMuntzGraphCokernelDilationAction_source]
  apply congrArg (coPoissonMuntzGraphSourceMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial))
  have composition := LinearMap.congr_fun
    (quarterDilationTestAction_comp
      (reversalCoPoissonMuntzParameter observation)
      (scaleSquare scale) (scaleSquare right)
      (scaleSquare_pos scale) (scaleSquare_pos right))
    (normalizedCoPoissonMuntzQuarterShellTest
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial))
  simpa only [LinearMap.comp_apply, scaleSquare_mul] using composition

end
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
