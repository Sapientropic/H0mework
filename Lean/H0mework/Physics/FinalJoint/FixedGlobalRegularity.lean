import H0mework.Physics.FinalJoint.FixedZeroFiber
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity

/-!
# Fixed P506/L0 final-common global regularity

The dependency-ordered common action write already produces one
four-dimensional holonomic configuration.  This module computes the
regularity of its nine surviving primitive fields directly:

* the final Einstein--Cartan write supplies an explicit normalized-affine
  Lorentz connection and recomputes `II+` plus its live reaction;
* the P286, scalar, primal-matter, and adjoint-matter writes are explicit
  affine or polynomial spacetime fields;
* every untouched field is inherited from the smooth recentered fixed
  P506/L0 input.

No regularity of an arbitrary Cartan restart, global inverse-coframe
premise, atlas, gluing receipt, residual inverse, target actual, or branch
choice is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeGravityGaugeRegularity
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineIIPlusRestriction
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineScalarActionSecondJetLocalActualLift
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance finalCommonP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance finalCommonP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance finalCommonP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem fixedP506L0RecenteredInput_smooth
    (space : StageNineSpatialPoint) :
    (fixedP506L0RecenteredInput space).Smooth := by
  exact
    spatiallyRecenterHolonomicConfiguration_smooth
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth space

theorem fixedP506L0FinalCommonActionActual_gravityConnection_contDiff
    (space : StageNineSpatialPoint)
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      (fixedP506L0FinalCommonActionActual space).gravityConnection point
        direction internalOut internalIn := by
  unfold fixedP506L0FinalCommonActionActual
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
    diracDualFormNativeECConstraintSurfaceConnectedActual
  exact normalizedAffineLorentzConnectionField_smooth _ _
    direction internalOut internalIn

theorem fixedP506L0FinalCommonActionActual_gravityAuxiliary_contDiff
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (fixedP506L0FinalCommonActionActual space).gravityAuxiliary point
        internalPair spacetimePair := by
  have auxiliarySmooth : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector
        ((fixedP506L0FinalCommonActionActual space).coframe point) :=
    physicalIIPlusBivector_contDiff.comp
      (fixedP506L0FinalCommonActionActual_coframe_contDiff space)
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector
      ((fixedP506L0FinalCommonActionActual space).coframe point)
        internalPair spacetimePair
  exact contDiff_pi.mp (contDiff_pi.mp auxiliarySmooth internalPair)
    spacetimePair

private theorem
    gravityConnectionDerivative_contDiff_of_connectionComponents
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction
          internalOut internalIn)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  let connectionCoordinate : BasePoint → ℝ := fun point =>
    configuration.gravityConnection point formDirection
      internalOut internalIn
  have coordinateSmooth : ContDiff ℝ ∞ connectionCoordinate :=
    connectionSmooth formDirection internalOut internalIn
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => connectionCoordinate)) := by
    exact coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ connectionCoordinate point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  unfold gravityConnectionDerivative
  change ContDiff ℝ ∞ fun point =>
    fderiv ℝ connectionCoordinate point
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

private theorem holonomicGravityCurvature_component_contDiff_of_connectionComponents
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction
          internalOut internalIn)
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature configuration point internal spacetime := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact gravityConnectionDerivative_contDiff_of_connectionComponents
        configuration connectionSmooth
        (pairFirst spacetime) (pairSecond spacetime)
        (pairFirst internal) (pairSecond internal)
    · exact gravityConnectionDerivative_contDiff_of_connectionComponents
        configuration connectionSmooth
        (pairSecond spacetime) (pairFirst spacetime)
        (pairFirst internal) (pairSecond internal)
  · apply ContDiff.sum
    intro middle _
    exact
      ((connectionSmooth (pairFirst spacetime)
          (pairFirst internal) middle).mul
        (connectionSmooth (pairSecond spacetime)
          middle (pairSecond internal))).sub
      ((connectionSmooth (pairSecond spacetime)
          (pairFirst internal) middle).mul
        (connectionSmooth (pairFirst spacetime)
          middle (pairSecond internal)))

theorem fixedP506L0FinalCommonActionActual_gravityCurvature_contDiff
    (space : StageNineSpatialPoint)
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature
        (fixedP506L0FinalCommonActionActual space) point
        internal spacetime := by
  exact holonomicGravityCurvature_component_contDiff_of_connectionComponents
    (fixedP506L0FinalCommonActionActual space)
    (fixedP506L0FinalCommonActionActual_gravityConnection_contDiff space)
    internal spacetime

theorem fixedP506L0FinalCommonActionActual_multiplier_contDiff
    (space : StageNineSpatialPoint)
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (fixedP506L0FinalCommonActionActual space).gravitySimplicityMultiplier
        point internal spacetime := by
  rw [show
    (fixedP506L0FinalCommonActionActual space).gravitySimplicityMultiplier =
        formNativeGravityReactionField
          (fixedP506L0FinalCommonActionActual space) by
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reactionSelfGenerated
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)]
  unfold formNativeGravityReactionField
  have auxiliarySmooth : ContDiff ℝ ∞ fun point =>
      (fixedP506L0FinalCommonActionActual space).gravityAuxiliary point := by
    apply contDiff_pi'
    intro internalPair
    apply contDiff_pi'
    intro spacetimePair
    exact
      fixedP506L0FinalCommonActionActual_gravityAuxiliary_contDiff
        space internalPair spacetimePair
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv
        ((fixedP506L0FinalCommonActionActual space).gravityAuxiliary point) := by
    change ContDiff ℝ ∞ fun point =>
      gravityInternalDualLinear
        ((fixedP506L0FinalCommonActionActual space).gravityAuxiliary point)
    exact
      gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
        auxiliarySmooth
  have contravariantCurvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature
          (fixedP506L0FinalCommonActionActual space) point
          internal spacetime := by
    exact contDiff_const.mul
      (fixedP506L0FinalCommonActionActual_gravityCurvature_contDiff
        space internal spacetime)
  exact
    (contDiff_pi.mp (contDiff_pi.mp dualSmooth internal) spacetime).sub
      contravariantCurvatureSmooth

theorem fixedP506L0FinalCommonActionActual_gaugeConnection_contDiff
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        ((fixedP506L0FinalCommonActionActual space).gaugeConnection point
          direction) := by
  rw [fixedP506L0FinalCommonActionActual_gaugeConnection,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_gaugeConnection,
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
  unfold recenteredContactActual
  rw [diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
  exact (fixedP506L0RecenteredInput_smooth space).2.2.2.2.1 direction

theorem fixedP506L0FinalCommonActionActual_gaugeAuxiliary_contDiff
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        ((fixedP506L0FinalCommonActionActual space).gaugeAuxiliary point
          pair) := by
  rw [fixedP506L0FinalCommonActionActual_gaugeAuxiliary]
  change ContDiff ℝ ∞ fun point =>
    p286CoordinateEquiv
      (formNativeCurrentP286CompleteResponseAuxiliaryField
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space)
        point pair)
  simpa [formNativeCurrentP286CompleteResponseAuxiliaryField] using
    formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_contDiff
      positiveSmoothUnifiedSource
      (recenteredCartanRepairedScalarSecondJetActual space) pair

private theorem scalarQuadraticTimeCorrection_contDiff_local
    (acceleration : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ (scalarQuadraticTimeCorrection acceleration) := by
  unfold scalarQuadraticTimeCorrection scalarQuadraticTimeCoefficient
  fun_prop

theorem fixedP506L0FinalCommonActionActual_scalar_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ (fixedP506L0FinalCommonActionActual space).scalar := by
  rw [fixedP506L0FinalCommonActionActual_scalar,
    recenteredCartanRepairedScalarSecondJetActual]
  change ContDiff ℝ ∞ fun point =>
    (fixedP506L0RecenteredInput space).scalar point +
      scalarQuadraticTimeCorrection
        (recenteredContactDiracDualScalarAcceleration space) point
  exact
    (fixedP506L0RecenteredInput_smooth space).2.2.2.2.2.2.1.add
      (scalarQuadraticTimeCorrection_contDiff_local
        (recenteredContactDiracDualScalarAcceleration space))

theorem fixedP506L0FinalCommonActionActual_matter_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        ((fixedP506L0FinalCommonActionActual space).matter point) := by
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((fixedP506L0FinalCommonActionActual space).matter point)) =
      (fun point =>
        matterCoordinateEquiv
            ((fixedP506L0RecenteredInput space).matter point) +
          matterLinearTimeCoordinateWrite
            (diracDualCurrentCoframeMatterTimeResponseWrite
              (fixedP506L0CartanRestartActual space)) point) by
    funext point
    rw [fixedP506L0FinalCommonActionActual_matter,
      recenteredCartanRepairedScalarSecondJetActual,
      installScalarQuadraticTimeCorrection_matter]
    change
      matterCoordinateEquiv
          ((actionGeneratedDiracDualRepairedMatterJointResponseActual
            (fixedP506L0CartanRestartActual space)).matter point) = _
    unfold actionGeneratedDiracDualRepairedMatterJointResponseActual
    rw [actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter]
    unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    rw [installMatterLinearTimeResponse_matter_coordinate]
    rw [show
      (fixedP506L0CartanRestartActual space).matter =
          (fixedP506L0RecenteredInput space).matter by
      exact
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
          positiveSmoothUnifiedSource (fixedP506L0RecenteredInput space)]
  ]
  exact
    (fixedP506L0RecenteredInput_smooth space).2.2.2.2.2.2.2.1.add
      (matterLinearTimeCoordinateWrite_contDiff
        (diracDualCurrentCoframeMatterTimeResponseWrite
          (fixedP506L0CartanRestartActual space)))

theorem fixedP506L0FinalCommonActionActual_conjugateMatter_contDiff
    (space : StageNineSpatialPoint)
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      (fixedP506L0FinalCommonActionActual space).conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index 1)) := by
  rw [← fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final]
  exact
    (fixedP506L0FinalCommonMatterSmoothComparison_smooth space).2.2.2.2.2.2.2.2
      index

/-- The source/action-generated fixed P506/L0 common successor is one
globally smooth four-dimensional nine-field actual. -/
theorem fixedP506L0FinalCommonActionActual_smooth
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  constructor
  · intro row column
    exact
      contDiff_pi.mp
        (contDiff_pi.mp
          (fixedP506L0FinalCommonActionActual_coframe_contDiff space) row)
        column
  constructor
  · exact fixedP506L0FinalCommonActionActual_gravityConnection_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_gravityAuxiliary_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_multiplier_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_gaugeConnection_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_gaugeAuxiliary_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_scalar_contDiff space
  constructor
  · exact fixedP506L0FinalCommonActionActual_matter_contDiff space
  · intro index
    rw [← fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final]
    exact
      (fixedP506L0FinalCommonMatterSmoothComparison_smooth space).2.2.2.2.2.2.2.2
        index

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
