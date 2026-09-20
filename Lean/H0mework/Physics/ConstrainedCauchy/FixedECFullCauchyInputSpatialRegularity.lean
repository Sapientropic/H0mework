import H0mework.Physics.FixedJoint.FixedCartanRestartCurvatureSpatialRegularity
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity

/-!
# Fixed P506/L0 full-Cauchy EC input regularity

This module proves spatial regularity of the two action-owned inputs consumed
by the final Einstein--Cartan write: the prepared evolution curvature and the
constraint action section generated from the evolved live stress.

Both profiles retain the fixed P506/L0 source/current lineage.  No final
constraint target, residual, branch, or acceptance certificate is used.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ECFullCauchyInputSpatialRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineTopologicalFourFormPairing
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

private theorem holonomicGravityCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gravityConnection = second.gravityConnection)
    (point : BasePoint) :
    holonomicGravityCurvature first point =
      holonomicGravityCurvature second point := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

private theorem fixedP506L0FinalCommonPreEC_preparedCurvature_eq_restart
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (fixedP506L0FinalCommonPreECActionActual space)) 0 =
      holonomicGravityCurvature
        (fixedP506L0CartanRestartActual space) 0 := by
  apply holonomicGravityCurvature_eq_of_connection_eq
  rw [diracDualFormNativeECNormalPreparedActual,
    restrictHolonomicConfigurationToIIPlus_gravityConnection,
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered,
    recenteredCartanRepairedConstitutiveCurrent_gravityConnection_eq_cartan]

private theorem fixedP506L0FinalCommonPreEC_preparedCurvature_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (fixedP506L0FinalCommonPreECActionActual space)) 0
        internalPair spacetimePair := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (fixedP506L0FinalCommonPreECActionActual space)) 0
        internalPair spacetimePair) =
      fun space =>
        holonomicGravityCurvature
          (fixedP506L0CartanRestartActual space) 0
          internalPair spacetimePair by
    funext space
    exact congrFun
      (congrFun
        (fixedP506L0FinalCommonPreEC_preparedCurvature_eq_restart space)
        internalPair)
      spacetimePair]
  exact
    fixedP506L0CartanRestartActual_curvature_origin_component_contDiff
      internalPair spacetimePair

private theorem fixedP506L0FinalCommonPreEC_identityLoad_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
        (coframeCoordinateDirection row column)) =
      fun space =>
        identityDiracDualECIntrinsicIIPlusObservation
            (coframeCoordinateDirection row column) +
          diracDualFormNativeECLiveNonGravityCoframeStress
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space)
            (coframeCoordinateDirection row column) by
    funext space
    unfold diracDualFormNativeIdentityECLoad
      identityDiracDualECIntrinsicIIPlusObservation
      diracDualFormNativeECLiveNonGravityCoframeStress
    simp only [add_apply]
    ring]
  exact contDiff_const.add
    (fixedP506L0FinalCommonPreECLiveNonGravityStress_coordinate_contDiff
      row column)

private theorem
    fixedP506L0FinalCommonPreEC_desiredEvolutionObservation_component_contDiff
    (row : Fin 4) (direction : Fin 3) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      diracDualFormNativeECDesiredEvolutionObservation
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
        row direction := by
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  exact
    (fixedP506L0FinalCommonPreEC_identityLoad_coordinate_contDiff
      row direction.succ).neg

private def totalEvolutionTemporalCoordinateProfile
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (internalPair : Fin 6) (direction : Fin 3)
    (space : StageNineSpatialPoint) : ℝ :=
  identityDiracDualECTemporalEvolutionTargetCoordinates
    (identityECTemporalCurvatureCoordinatesOf (current space))
    (desired space -
      identityDiracDualECTemporalEvolutionObservation
        (identityECSpatialCurvaturePart (current space)))
    internalPair direction

private theorem totalEvolutionTemporalCoordinateProfile_zero_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 0 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem totalEvolutionTemporalCoordinateProfile_one_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 1 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem totalEvolutionTemporalCoordinateProfile_two_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 2 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem totalEvolutionTemporalCoordinateProfile_three_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 3 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem totalEvolutionTemporalCoordinateProfile_four_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 4 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem totalEvolutionTemporalCoordinateProfile_five_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile current desired 5 direction) := by
  unfold totalEvolutionTemporalCoordinateProfile
  fin_cases direction <;>
    simp [identityDiracDualECTemporalEvolutionTargetCoordinates,
      identityDiracDualECTemporalEvolutionKernelPart,
      identityDiracDualECTemporalEvolutionSectionCoordinates,
      identityDiracDualECTemporalEvolutionObservation,
      identityECTemporalCurvatureCoordinatesOf,
      identityECTemporalCurvatureOfCoordinates,
      identityECSpatialCurvaturePart,
      identityECTemporalCurvaturePart,
      identityECTemporalSpatialPair,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection,
      physicalIIPlusCoframeTangent,
      coframeWedgeTangent,
      gravityInternalPairVarianceNormalization_apply,
      internalBivectorDual, lorentzianCoframeHodge, Matrix.trace,
      Matrix.vecHead, Matrix.vecTail, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, Fin.sum_univ_six] <;>
    fun_prop (disch := first | exact currentSmooth _ _ |
      exact desiredSmooth _ _)

private theorem
    totalEvolutionTemporalCoordinates_component_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (internalPair : Fin 6) (direction : Fin 3) :
    ContDiff ℝ ∞
      (totalEvolutionTemporalCoordinateProfile
        current desired internalPair direction) := by
  fin_cases internalPair
  · exact totalEvolutionTemporalCoordinateProfile_zero_contDiff
      current desired currentSmooth desiredSmooth direction
  · exact totalEvolutionTemporalCoordinateProfile_one_contDiff
      current desired currentSmooth desiredSmooth direction
  · exact totalEvolutionTemporalCoordinateProfile_two_contDiff
      current desired currentSmooth desiredSmooth direction
  · exact totalEvolutionTemporalCoordinateProfile_three_contDiff
      current desired currentSmooth desiredSmooth direction
  · exact totalEvolutionTemporalCoordinateProfile_four_contDiff
      current desired currentSmooth desiredSmooth direction
  · exact totalEvolutionTemporalCoordinateProfile_five_contDiff
      current desired currentSmooth desiredSmooth direction

private theorem totalEvolutionCurvatureTarget_component_contDiff
    (current : StageNineSpatialPoint → PhysicalBivector)
    (desired :
      StageNineSpatialPoint → IdentityECSpatialCoframeCovectorCoordinates)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (desiredSmooth : ∀ row direction,
      ContDiff ℝ ∞ fun space =>
        desired space row direction)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair spacetimePair := by
  fin_cases spacetimePair
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (0 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (0 : Fin 6)) =
        fun space =>
          identityDiracDualECTemporalEvolutionTargetCoordinates
            (identityECTemporalCurvatureCoordinatesOf (current space))
            (desired space -
              identityDiracDualECTemporalEvolutionObservation
                (identityECSpatialCurvaturePart (current space)))
            internalPair (0 : Fin 3) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_temporal
        (current space) (desired space) internalPair 0]
    exact totalEvolutionTemporalCoordinates_component_contDiff
      current desired currentSmooth desiredSmooth internalPair 0
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (1 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (1 : Fin 6)) =
        fun space =>
          identityDiracDualECTemporalEvolutionTargetCoordinates
            (identityECTemporalCurvatureCoordinatesOf (current space))
            (desired space -
              identityDiracDualECTemporalEvolutionObservation
                (identityECSpatialCurvaturePart (current space)))
            internalPair (1 : Fin 3) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_temporal
        (current space) (desired space) internalPair 1]
    exact totalEvolutionTemporalCoordinates_component_contDiff
      current desired currentSmooth desiredSmooth internalPair 1
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (2 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (2 : Fin 6)) =
        fun space =>
          identityDiracDualECTemporalEvolutionTargetCoordinates
            (identityECTemporalCurvatureCoordinatesOf (current space))
            (desired space -
              identityDiracDualECTemporalEvolutionObservation
                (identityECSpatialCurvaturePart (current space)))
            internalPair (2 : Fin 3) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_temporal
        (current space) (desired space) internalPair 2]
    exact totalEvolutionTemporalCoordinates_component_contDiff
      current desired currentSmooth desiredSmooth internalPair 2
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (3 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (3 : Fin 6)) =
        fun space => current space internalPair (3 : Fin 6) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (current space) (desired space) internalPair 0]
    exact currentSmooth internalPair 3
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (4 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (4 : Fin 6)) =
        fun space => current space internalPair (4 : Fin 6) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (current space) (desired space) internalPair 1]
    exact currentSmooth internalPair 4
  · change ContDiff ℝ ∞ fun space =>
      identityDiracDualECTotalEvolutionCurvatureTarget
        (current space) (desired space) internalPair (5 : Fin 6)
    rw [show
      (fun space =>
        identityDiracDualECTotalEvolutionCurvatureTarget
          (current space) (desired space) internalPair (5 : Fin 6)) =
        fun space => current space internalPair (5 : Fin 6) by
      funext space
      exact identityDiracDualECTotalEvolutionCurvatureTarget_spatial
        (current space) (desired space) internalPair 2]
    exact currentSmooth internalPair 5

private theorem fixedP506L0FinalCommonPreEC_cauchyCurvatureTarget_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      diracDualFormNativeECCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
        internalPair spacetimePair := by
  unfold diracDualFormNativeECCauchyCurvatureTarget
    diracDualFormNativeECCauchyCurrentCurvature
  exact
    totalEvolutionCurvatureTarget_component_contDiff
      (fun space =>
        holonomicGravityCurvature
          (diracDualFormNativeECNormalPreparedActual
            (fixedP506L0FinalCommonPreECActionActual space)) 0)
      (fun space =>
        diracDualFormNativeECDesiredEvolutionObservation
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space))
      fixedP506L0FinalCommonPreEC_preparedCurvature_component_contDiff
      fixedP506L0FinalCommonPreEC_desiredEvolutionObservation_component_contDiff
      internalPair spacetimePair

private theorem
    fixedP506L0FinalCommonPreEC_evolutionPreparedCurvature_eq_target
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))) 0 =
      diracDualFormNativeECCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space) := by
  calc
    holonomicGravityCurvature
          (diracDualFormNativeECNormalPreparedActual
            (diracDualFormNativeECEvolutionWrittenCurrent
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual space))) 0 =
        holonomicGravityCurvature
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space)) 0 := by
      apply holonomicGravityCurvature_eq_of_connection_eq
      exact restrictHolonomicConfigurationToIIPlus_gravityConnection _
    _ = diracDualFormNativeECCauchyCurvatureTarget
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space) := by
      exact
        sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_curvature_zero
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space)

/-- Every coordinate of the prepared curvature consumed by the constraint
write is smooth on the fixed P506/L0 spatial lineage. -/
theorem
    fixedP506L0FinalCommonPreECEvolutionPreparedCurvature_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))) 0
        internalPair spacetimePair := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (diracDualFormNativeECNormalPreparedActual
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))) 0
        internalPair spacetimePair) =
      fun space =>
        diracDualFormNativeECCauchyCurvatureTarget
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space)
          internalPair spacetimePair by
    funext space
    exact congrFun
      (congrFun
        (fixedP506L0FinalCommonPreEC_evolutionPreparedCurvature_eq_target
          space)
        internalPair)
      spacetimePair]
  exact
    fixedP506L0FinalCommonPreEC_cauchyCurvatureTarget_component_contDiff
      internalPair spacetimePair

private theorem constraintActionSection_component_contDiff_of_stressCoordinates
    (stress :
      StageNineSpatialPoint → LorentzianCoframe →L[ℝ] ℝ)
    (stressSmooth : ∀ row column,
      ContDiff ℝ ∞ fun space =>
        stress space (coframeCoordinateDirection row column))
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      identityDiracDualECConstraintActionSection
        (stress space) internalPair spacetimePair := by
  unfold identityDiracDualECConstraintActionSection
    identityDiracDualECConstraintActionRaisedCurvature
    identityDiracDualECConstraintActionReaction
    identityDiracDualECConstraintActionResponse
    linearPlebanskiMultiplierOfCoframeResponse
    linearPlebanskiCoframeResponseOfStress
    linearPlebanskiTraceReverse
    coframeCovectorCoordinates
    gravityInternalPairVarianceNormalization
  fin_cases internalPair <;>
    simp [internalBivectorDual, lorentzianCoframeHodge,
      physicalIIPlusCoframeTangent, coframeWedgeTangent, Matrix.trace] <;>
    fun_prop (disch := exact stressSmooth _ _)

private theorem fixedP506L0FinalCommonPreEC_constraintActionSection_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      identityDiracDualECConstraintActionSection
        (diracDualFormNativeECLiveNonGravityCoframeStress
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space))
        internalPair spacetimePair := by
  exact
    constraintActionSection_component_contDiff_of_stressCoordinates
      (fun space =>
        diracDualFormNativeECLiveNonGravityCoframeStress
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space))
      fixedP506L0FinalCommonPreECLiveNonGravityStress_coordinate_contDiff
      internalPair spacetimePair

private theorem fixedP506L0FinalCommonPreEC_evolutionLiveStress_eq
    (space : StageNineSpatialPoint) :
    diracDualFormNativeECLiveNonGravityCoframeStress
        positiveSmoothUnifiedSource
        (diracDualFormNativeECEvolutionWrittenCurrent
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space)) =
      diracDualFormNativeECLiveNonGravityCoframeStress
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space) := by
  unfold diracDualFormNativeECLiveNonGravityCoframeStress
    diracDualFormNativeECEvolutionWrittenCurrent
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_gaugeEuler_preserved,
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_matterEuler_preserved]

/-- Every coordinate of the constraint action section recomputed on the
evolution output is smooth on the same fixed P506/L0 lineage. -/
theorem
    fixedP506L0FinalCommonPreECEvolutionConstraintActionSection_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      identityDiracDualECConstraintActionSection
        (diracDualFormNativeECLiveNonGravityCoframeStress
          positiveSmoothUnifiedSource
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space)))
        internalPair spacetimePair := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      identityDiracDualECConstraintActionSection
        (diracDualFormNativeECLiveNonGravityCoframeStress
          positiveSmoothUnifiedSource
          (diracDualFormNativeECEvolutionWrittenCurrent
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space)))
        internalPair spacetimePair) =
      fun space =>
        identityDiracDualECConstraintActionSection
          (diracDualFormNativeECLiveNonGravityCoframeStress
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))
          internalPair spacetimePair by
    funext space
    rw [fixedP506L0FinalCommonPreEC_evolutionLiveStress_eq]]
  exact
    fixedP506L0FinalCommonPreEC_constraintActionSection_component_contDiff
      internalPair spacetimePair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ECFullCauchyInputSpatialRegularity
