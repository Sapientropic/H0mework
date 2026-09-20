import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyInputSpatialRegularity
import H0mework.Physics.IdentityGerms.CoframeHessianSection

/-!
# Fixed P506/L0 full-Cauchy curvature-target spatial regularity

The complete Einstein--Cartan writer generates its curvature target from the
same fixed P506/L0 source and pre-EC current.  This module proves coordinate
regularity of that generated target in the source-owned spatial occurrence.
No target value, residual, branch, field equation, or smoothness receipt is
accepted as input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ECFullCauchyCurvatureTargetSpatialRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506ECFullCauchyInputSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private def fixedECCurvatureObservationCoordinateLinear
    (row column : LorentzianIndex) :
    PhysicalBivector →ₗ[ℝ] ℝ where
  toFun := fun rawCurvature =>
    identityDiracDualECCurvatureObservation rawCurvature
      (coframeCoordinateDirection row column)
  map_add' := by
    intro first second
    rw [identityDiracDualECCurvatureObservation_add]
    rfl
  map_smul' := by
    intro parameter rawCurvature
    unfold identityDiracDualECCurvatureObservation
    change
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
            (coframeCoordinateDirection row column))
          (gravityInternalPairVarianceNormalization
            (parameter • rawCurvature)) =
        parameter *
          gravityTopologicalWedgeCoefficient
            (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
              (coframeCoordinateDirection row column))
            (gravityInternalPairVarianceNormalization rawCurvature)
    rw [map_smul, gravityTopologicalWedgeCoefficient_smul_right]

private def fixedECCurvatureObservationCoordinates
    (rawCurvature : PhysicalBivector) : LorentzianCoframe :=
  coframeCovectorCoordinates
    (identityDiracDualECCurvatureObservation rawCurvature)

private def fixedECConstraintReplacementCoordinates
    (current actionCurvature : PhysicalBivector) : LorentzianCoframe :=
  coframeCovectorCoordinates
    (identityECConstraintReplacementObservation
      (identityDiracDualECCurvatureObservation current)
      (identityDiracDualECCurvatureObservation actionCurvature))

private def fixedECNormalSectionOfCoordinates
    (coordinates : LorentzianCoframe) : PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    (linearPlebanskiMultiplierOfCoframeResponse
      (linearPlebanskiTraceReverse coordinates))

private theorem fixedECCurvatureObservationCoordinates_contDiff
    (curvature : StageNineSpatialPoint → PhysicalBivector)
    (curvatureSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        curvature space internalPair spacetimePair) :
    ContDiff ℝ ∞ fun space =>
      fixedECCurvatureObservationCoordinates (curvature space) := by
  have curvatureContDiff : ContDiff ℝ ∞ curvature := by
    apply contDiff_pi'
    intro internalPair
    apply contDiff_pi'
    intro spacetimePair
    exact curvatureSmooth internalPair spacetimePair
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold fixedECCurvatureObservationCoordinates
    coframeCovectorCoordinates
  change ContDiff ℝ ∞
    (fun space =>
      (fixedECCurvatureObservationCoordinateLinear row column
        ).toContinuousLinearMap (curvature space))
  exact
    (fixedECCurvatureObservationCoordinateLinear row column)
      |>.toContinuousLinearMap.contDiff.comp curvatureContDiff

private theorem fixedECConstraintReplacementCoordinates_contDiff
    (current actionCurvature :
      StageNineSpatialPoint → PhysicalBivector)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (actionSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        actionCurvature space internalPair spacetimePair) :
    ContDiff ℝ ∞ fun space =>
      fixedECConstraintReplacementCoordinates
        (current space) (actionCurvature space) := by
  have currentObservationSmooth :=
    fixedECCurvatureObservationCoordinates_contDiff
      current currentSmooth
  have actionObservationSmooth :=
    fixedECCurvatureObservationCoordinates_contDiff
      actionCurvature actionSmooth
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold fixedECConstraintReplacementCoordinates
    coframeCovectorCoordinates
  simp only [Matrix.of_apply]
  rw [show
    (fun space =>
      identityECConstraintReplacementObservation
          (identityDiracDualECCurvatureObservation (current space))
          (identityDiracDualECCurvatureObservation
            (actionCurvature space))
          (coframeCoordinateDirection row column)) =
      fun space =>
        if column = 0 then
          fixedECCurvatureObservationCoordinates
              (actionCurvature space) row column
        else
          fixedECCurvatureObservationCoordinates
              (current space) row column by
    funext space
    rw [identityECConstraintReplacementObservation_coordinateDirection]
    rfl]
  split_ifs
  · exact
      contDiff_pi.mp
        (contDiff_pi.mp actionObservationSmooth row) column
  · exact
      contDiff_pi.mp
        (contDiff_pi.mp currentObservationSmooth row) column

private theorem fixedECNormalSectionOfCoordinates_component_contDiff
    (coordinates : StageNineSpatialPoint → LorentzianCoframe)
    (coordinatesSmooth : ContDiff ℝ ∞ coordinates)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      fixedECNormalSectionOfCoordinates (coordinates space)
        internalPair spacetimePair := by
  simp only [fixedECNormalSectionOfCoordinates,
    gravityInternalPairVarianceNormalization_apply]
  unfold linearPlebanskiMultiplierOfCoframeResponse
    linearPlebanskiTraceReverse
    physicalIIPlusCoframeTangent
    coframeWedgeTangent
  simp only [Matrix.of_apply]
  fin_cases internalPair <;>
    simp [internalBivectorDual, lorentzianCoframeHodge] <;>
    fun_prop

private theorem
    identityDiracDualECConstraintReplacementCurvatureTarget_component_contDiff
    (current actionCurvature :
      StageNineSpatialPoint → PhysicalBivector)
    (currentSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        current space internalPair spacetimePair)
    (actionSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun space =>
        actionCurvature space internalPair spacetimePair)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      identityDiracDualECConstraintReplacementCurvatureTarget
        (current space) (actionCurvature space)
        internalPair spacetimePair := by
  have currentCoordinatesSmooth :=
    fixedECCurvatureObservationCoordinates_contDiff
      current currentSmooth
  have replacementCoordinatesSmooth :=
    fixedECConstraintReplacementCoordinates_contDiff
      current actionCurvature currentSmooth actionSmooth
  rw [show
    (fun space =>
      identityDiracDualECConstraintReplacementCurvatureTarget
          (current space) (actionCurvature space)
          internalPair spacetimePair) =
      fun space =>
        current space internalPair spacetimePair -
          fixedECNormalSectionOfCoordinates
              (-fixedECCurvatureObservationCoordinates
                (current space))
              internalPair spacetimePair +
          fixedECNormalSectionOfCoordinates
              (-fixedECConstraintReplacementCoordinates
                (current space) (actionCurvature space))
              internalPair spacetimePair by
    funext space
    unfold identityDiracDualECConstraintReplacementCurvatureTarget
      identityDiracDualECCurvatureTarget
      identityDiracDualECCurvatureKernelPart
      identityDiracDualECCurvatureNormalSection
      fixedECNormalSectionOfCoordinates
      fixedECCurvatureObservationCoordinates
      fixedECConstraintReplacementCoordinates
      linearPlebanskiCoframeResponseOfStress
    rw [coframeCovectorCoordinates_neg,
      coframeCovectorCoordinates_neg]
    rfl]
  exact
    (currentSmooth internalPair spacetimePair).sub
      (fixedECNormalSectionOfCoordinates_component_contDiff
        (fun space =>
          -fixedECCurvatureObservationCoordinates (current space))
        currentCoordinatesSmooth.neg
        internalPair spacetimePair)
      |>.add
        (fixedECNormalSectionOfCoordinates_component_contDiff
          (fun space =>
            -fixedECConstraintReplacementCoordinates
              (current space) (actionCurvature space))
          replacementCoordinatesSmooth.neg
          internalPair spacetimePair)

/-- Every component of the full EC curvature target generated from the
fixed pre-EC current is smooth in its source-owned spatial occurrence. -/
theorem
    fixedP506L0FinalCommonPreECFullCauchyCurvatureTarget_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
        internalPair spacetimePair := by
  unfold sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
    diracDualFormNativeECConstraintSurfaceCurvatureTarget
    diracDualFormNativeECConstraintSurfaceCurrentCurvature
    diracDualFormNativeECConstraintActionCurvature
  exact
    identityDiracDualECConstraintReplacementCurvatureTarget_component_contDiff
      (fun space =>
        holonomicGravityCurvature
          (diracDualFormNativeECNormalPreparedActual
            (diracDualFormNativeECEvolutionWrittenCurrent
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual space))) 0)
      (fun space =>
        identityDiracDualECConstraintActionSection
          (diracDualFormNativeECLiveNonGravityCoframeStress
            positiveSmoothUnifiedSource
            (diracDualFormNativeECEvolutionWrittenCurrent
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual space))))
      fixedP506L0FinalCommonPreECEvolutionPreparedCurvature_component_contDiff
      fixedP506L0FinalCommonPreECEvolutionConstraintActionSection_component_contDiff
      internalPair spacetimePair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ECFullCauchyCurvatureTargetSpatialRegularity
