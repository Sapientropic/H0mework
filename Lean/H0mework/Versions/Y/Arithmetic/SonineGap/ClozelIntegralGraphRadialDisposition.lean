import H0mework.Versions.Y.Arithmetic.SonineGap.ClozelIntegralGraphCovarianceDisposition
import H0mework.Versions.Y.Arithmetic.Muntz.GraphContact.ClozelGraphActionContactResidual

/-!
# Radial disposition of the integral graph covariance

At the actual scale-three action, the generic integral/coherent radial
residual on the identity charge is the negative of the existing graph-action
norm residual on the normalized Mellin shell.  Its zero fibre is therefore
exactly the critical half-density condition.  The vector residual remains a
strictly stronger phase-sensitive coordinate.
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

open Character.GlobalCoPoissonCurrent
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCovariance
open ThetaJRoleRepresentation

noncomputable section

theorem scaleSquare_stageSqrtScaleUnit_zero :
    scaleSquare (stageSqrtScaleUnit 0) =
      positiveMellinQuarterNoGoScale := by
  unfold scaleSquare stageSqrtScaleUnit scaleValue
    positiveMellinQuarterNoGoScale
  rw [SourceGeneratedPositiveRealCharacter.positiveRealUnit_val,
    Real.sq_sqrt (by positivity)]
  norm_num [QRich.blockQRichSuccessorScale_eq_stage_add_three]

theorem quarterScaleThreeTestAction_eq_quarterDilationTestAction
    (z : ℂ) :
    quarterScaleThreeTestAction z =
      quarterDilationTestAction z positiveMellinQuarterNoGoScale
        positiveMellinQuarterNoGoScale_pos := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  rfl

theorem selectedIntegralGraphCovariance_radialResidual_delta_one_eq_neg_graphAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    radialResidual
        (selectedIntegralGraphCovarianceAction observation nontrivial
          (stageSqrtScaleUnit 0)) (delta 1) =
      - graphActionNormResidual
          (zeroOwnedQuarterGraphCovariance observation)
          (normalizedCoPoissonMuntzQuarterShellTest
            (selectedCoPoissonMuntzParameter observation)
            (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)) := by
  unfold radialResidual selectedIntegralGraphCovarianceAction
  rw [LinearIsometry.norm_map]
  rw [selectedIntegralGraphOrbit_delta]
  change
    ‖selectedGraphOrbitBasis observation nontrivial 1‖ -
      ‖selectedIntegralGraphOrbit observation nontrivial
        ((leftTranslation (stageSqrtScaleUnit 0)).toLinearMap (delta 1))‖ = _
  have translated :
      (leftTranslation (stageSqrtScaleUnit 0)).toLinearMap (delta 1) =
        delta (stageSqrtScaleUnit 0) := by
    calc
      _ = delta (stageSqrtScaleUnit 0 * 1) :=
        leftTranslation_delta (stageSqrtScaleUnit 0) 1
      _ = delta (stageSqrtScaleUnit 0) := by simp
  rw [translated, selectedIntegralGraphOrbit_delta]
  change
    ‖selectedGraphOrbitBasis observation nontrivial 1‖ -
      ‖selectedGraphOrbitBasis observation nontrivial
        (stageSqrtScaleUnit 0)‖ = _
  unfold graphActionNormResidual
  let test := normalizedCoPoissonMuntzQuarterShellTest
    (observation.coordinate / 2)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
  have basisOne :
      selectedGraphOrbitBasis observation nontrivial 1 =
        graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
          (quarterMellinL2Functional (observation.coordinate / 2)) test := by
    unfold selectedGraphOrbitBasis
    change graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2))
        (quarterDilationTestAction (observation.coordinate / 2)
          (scaleSquare 1) (scaleSquare_pos 1) test) = _
    have actionOne := LinearMap.congr_fun
      (quarterDilationTestAction_one (observation.coordinate / 2)) test
    simpa [scaleSquare, scaleValue] using congrArg
      (graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2))) actionOne
  have basisScale :
      selectedGraphOrbitBasis observation nontrivial
          (stageSqrtScaleUnit 0) =
        graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
          (quarterMellinL2Functional (observation.coordinate / 2))
          ((zeroOwnedQuarterGraphCovariance observation).sourceAction test) := by
    unfold selectedGraphOrbitBasis
    change graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2))
        (quarterDilationTestAction (observation.coordinate / 2)
          (scaleSquare (stageSqrtScaleUnit 0))
          (scaleSquare_pos (stageSqrtScaleUnit 0)) test) = _
    have actionScale := LinearMap.congr_fun
      (quarterScaleThreeTestAction_eq_quarterDilationTestAction
        (observation.coordinate / 2)) test
    change graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2))
        (quarterDilationTestAction (observation.coordinate / 2)
          (scaleSquare (stageSqrtScaleUnit 0))
          (scaleSquare_pos (stageSqrtScaleUnit 0)) test) =
      graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2))
        (quarterScaleThreeTestAction (observation.coordinate / 2) test)
    simpa [scaleSquare_stageSqrtScaleUnit_zero] using congrArg
      (graphFeature (quarterMellinL2Feature (observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2)))
      actionScale.symm
  rw [basisOne, basisScale]
  have testEq :
      normalizedCoPoissonMuntzQuarterShellTest
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial) =
        test := by
    rfl
  rw [testEq]
  ring

theorem selectedIntegralGraphCovariance_radialResidual_delta_one_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    radialResidual
        (selectedIntegralGraphCovarianceAction observation nontrivial
          (stageSqrtScaleUnit 0)) (delta 1) = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  let z := observation.coordinate / 2
  let test := normalizedCoPoissonMuntzQuarterShellTest z
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
  let covariance := zeroOwnedQuarterGraphCovariance observation
  constructor
  · intro radialZero
    have graphResidualZero :
        graphActionNormResidual covariance test = 0 := by
      have bridge :=
        selectedIntegralGraphCovariance_radialResidual_delta_one_eq_neg_graphAction
          observation nontrivial
      rw [radialZero] at bridge
      have testEq :
          normalizedCoPoissonMuntzQuarterShellTest
              (selectedCoPoissonMuntzParameter observation)
              (selectedCoPoissonMuntzParameter_re_pos observation nontrivial) =
            test := by
        rfl
      rw [testEq] at bridge
      exact neg_eq_zero.mp bridge.symm
    have graphNorm := sub_eq_zero.mp graphResidualZero
    have graphNormSq := congrArg (fun normValue : ℝ => normValue ^ 2) graphNorm
    rw [WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2] at graphNormSq
    change
        ‖quarterMellinL2Feature z (covariance.sourceAction test)‖ ^ 2 +
            ‖quarterMellinL2Functional z (covariance.sourceAction test)‖ ^ 2 =
          ‖quarterMellinL2Feature z test‖ ^ 2 +
            ‖quarterMellinL2Functional z test‖ ^ 2 at graphNormSq
    have featureCovariance := LinearMap.congr_fun
      covariance.feature_covariance test
    change covariance.hilbertAction (quarterMellinL2Feature z test) =
      quarterMellinL2Feature z (covariance.sourceAction test) at featureCovariance
    have featureNorm :
        ‖quarterMellinL2Feature z (covariance.sourceAction test)‖ =
          ‖quarterMellinL2Feature z test‖ := by
      rw [← featureCovariance]
      change ‖quarterScaleThreeEnergyAction
          (quarterMellinL2Feature z test)‖ =
        ‖quarterMellinL2Feature z test‖
      rw [quarterScaleThreeEnergyAction_apply]
      exact (positiveMellinQuarterEnergyTranslationIsometry
        (Real.log positiveMellinQuarterNoGoScale)).norm_map _
    have functionalCovariance := LinearMap.congr_fun
      covariance.functional_eigenlaw test
    change quarterMellinL2Functional z (covariance.sourceAction test) =
      covariance.character • quarterMellinL2Functional z test at functionalCovariance
    have functionalOne : quarterMellinL2Functional z test = 1 := by
      exact quarterMellinL2Functional_normalizedShell z
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    rw [featureNorm, functionalCovariance, functionalOne,
      smul_eq_mul, mul_one, norm_one] at graphNormSq
    have characterNormNonneg : 0 ≤ ‖covariance.character‖ := norm_nonneg _
    have characterNormOne : ‖covariance.character‖ = 1 := by
      nlinarith
    have fixed : observation.coordinate =
        coordinateReversal observation.coordinate := by
      exact (quarterGraph_character_norm_one_iff_coordinate_eq_reversal
        observation).1 characterNormOne
    have realFixed := congrArg Complex.re fixed
    simp [coordinateReversal] at realFixed
    linarith
  · intro critical
    have fixed : observation.coordinate =
        coordinateReversal observation.coordinate := by
      apply Complex.ext
      · simp [coordinateReversal]
        linarith
      · simp [coordinateReversal]
    have characterNormOne :=
      (quarterGraph_character_norm_one_iff_coordinate_eq_reversal
        observation).2 fixed
    have graphResidualZero :
        graphActionNormResidual covariance test = 0 :=
      quarterGraph_source_residual_zero_of_character_norm_one
        observation characterNormOne test
    rw [selectedIntegralGraphCovariance_radialResidual_delta_one_eq_neg_graphAction]
    have testEq :
        normalizedCoPoissonMuntzQuarterShellTest
            (selectedCoPoissonMuntzParameter observation)
            (selectedCoPoissonMuntzParameter_re_pos observation nontrivial) =
          test := by
      rfl
    rw [testEq]
    rw [graphResidualZero, neg_zero]

end

end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
