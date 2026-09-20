import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity
import H0mework.Physics.DualVariation.RecenteredScalarSecondJetActionResponse
import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointFirstJet
import H0mework.Physics.RepairedAction.ActionSpatialSectionRecenterContactResidualNormalForm
import H0mework.Physics.FinalJoint.FixedActionWrite
import H0mework.Physics.GaugeAction.P286ActionConnectionVelocity

/-!
# Fixed P506/L0 scalar-acceleration spatial regularity

The repaired mother action generates one scalar acceleration at every matching
P506/L0 spatial contact.  This module proves that those action-generated
coordinates form a `C∞` spatial profile.  No residual, support coordinate,
target acceleration, branch choice, or inverse witness is accepted at the
theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ScalarAccelerationSpatialRegularity

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterContactResidualNormalForm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-! ## Smooth action readout on the canonical zero slice -/

private theorem inputScalarMomentum_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
        direction derivativeDirection)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeSmooth : ContDiff ℝ ∞ InputActual.coframe :=
    holonomicCoframe_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have coframeAtPoint : InputActual.coframe point = 1 :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have coframeNondegenerate : Matrix.det (InputActual.coframe point) ≠ 0 := by
    rw [coframeAtPoint]
    norm_num
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (InputActual.coframe candidate)|) point :=
    (coframe_volume_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (InputActual.coframe candidate))⁻¹)
      point :=
    (lorentzianMetric_inv_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun candidate =>
        holonomicScalarCovariantDerivative InputActual candidate
          formDirection :=
    holonomicScalarCovariantDerivative_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth formDirection
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection :=
    contDiff_const
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
  exact
    ((scalarCoordinatePairingRe_joint_contDiff_local _ _
      (variationSmooth first) (covariantSmooth second)).add
      (scalarCoordinatePairingRe_joint_contDiff_local _ _
        (covariantSmooth first) (variationSmooth second))).contDiffAt

private theorem inputScalarMomentumDerivative_zeroSlice_contDiff
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
          direction derivativeDirection)
        (canonicalCauchySlicePoint 0 space) derivativeDirection := by
  rw [contDiff_iff_contDiffAt]
  intro space
  let momentum :=
    scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
      direction derivativeDirection
  have momentumSmooth : ContDiffAt ℝ ∞ momentum
      (canonicalCauchySlicePoint 0 space) :=
    inputScalarMomentum_contDiffAt_zeroSlice space direction
      derivativeDirection
  have jointSmooth : ContDiffAt ℝ ∞
      (Function.uncurry (fun _ : StageNineSpatialPoint => momentum))
      (space, canonicalCauchySlicePoint 0 space) :=
    momentumSmooth.comp
      (space, canonicalCauchySlicePoint 0 space) contDiffAt_snd
  have sliceSmooth : ContDiffAt ℝ ∞ (canonicalCauchySlicePoint 0) space := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext candidate
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [canonicalCauchySlicePoint, canonicalSpatialInclusion,
          canonicalSpatialCoordinate, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]]
    exact canonicalSpatialInclusion.contDiff.contDiffAt
  have derivativeSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        fderiv ℝ momentum (canonicalCauchySlicePoint 0 candidate)) space := by
    simpa only [Function.uncurry_apply_pair] using
      jointSmooth.fderiv sliceSmooth (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeSmooth.clm_apply contDiffAt_const

private theorem inputScalarDivergence_zeroSlice_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun space =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        InputActual direction (canonicalCauchySlicePoint 0 space) := by
  unfold scalarDifferentialMomentumDivergence
  apply ContDiff.sum
  intro derivativeDirection _
  exact inputScalarMomentumDerivative_zeroSlice_contDiff direction
    derivativeDirection

/-! ## Algebraic scalar-action leg -/

private def inputWithConstantScalar
    (direction : ScalarCoordinateCarrier) : StageNineHolonomicConfiguration :=
  { InputActual with scalar := fun _ => direction }

private theorem inputWithConstantScalar_smooth
    (direction : ScalarCoordinateCarrier) :
    (inputWithConstantScalar direction).Smooth := by
  rcases fixedP506FormNativeJointActionSolvedSuccessor_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, gaugeAuxiliary, _, matter, conjugateMatter⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, gaugeAuxiliary, contDiff_const, matter,
      conjugateMatter⟩

private theorem inputScalarVariation_contDiff
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (InputActual.gaugeConnection point formDirection))
        direction := by
  simpa [inputWithConstantScalar] using
    (StageNineCoframeScalarMatterRegularity.holonomicScalarP286Action_contDiff_local
      (inputWithConstantScalar direction)
      (inputWithConstantScalar_smooth direction) formDirection)

private theorem inputScalarYukawaVectorCoordinates_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField InputActual point) direction) := by
  have actual :=
    (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : BasePoint => direction))).clm_apply
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
  change ContDiff ℝ ∞ fun point =>
    matterCoordinateEquiv
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm direction)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (InputActual.matter point)))) at actual
  simpa only [diracDualScalarYukawaVariationVector, toContinuumPointField,
    matterCoordinateEquiv.symm_apply_apply] using actual

private theorem inputScalarYukawa_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun point =>
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField InputActual point) direction := by
  have vectorSmooth := inputScalarYukawaVectorCoordinates_contDiff direction
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (InputActual.conjugateMatter point) := by
    change ContDiff ℝ ∞
      (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates
        InputActual)
    exact
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates_contDiff
        InputActual fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have complexSmooth : ContDiff ℝ ∞ fun point =>
      InputActual.conjugateMatter point
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField InputActual point) direction) := by
    let pairingSum : BasePoint → ℂ := fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField InputActual point) direction) index *
          matterDualCoordinates (InputActual.conjugateMatter point) index
    have pairingEquality : (fun point =>
        InputActual.conjugateMatter point
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField InputActual point) direction)) = pairingSum := by
      funext point
      rw [← matterDualOfCoordinates_surjective
        (InputActual.conjugateMatter point)]
      exact matterDualOfCoordinates_apply _ _
    rw [pairingEquality]
    unfold pairingSum
    apply ContDiff.sum
    intro index _
    have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField InputActual point) direction) index := by
      change ContDiff ℝ ∞
        (((EuclideanSpace.proj index).restrictScalars ℝ) ∘
          fun point =>
            matterCoordinateEquiv
              (diracDualScalarYukawaVariationVector
                (toContinuumPointField InputActual point) direction))
      exact ((EuclideanSpace.proj index).restrictScalars ℝ).contDiff.comp
        vectorSmooth
    have dualCoordinateSmooth : ContDiff ℝ ∞ fun point =>
        matterDualCoordinates (InputActual.conjugateMatter point) index := by
      change ContDiff ℝ ∞
        (((EuclideanSpace.proj index).restrictScalars ℝ) ∘
          fun point => matterDualCoordinates (InputActual.conjugateMatter point))
      exact ((EuclideanSpace.proj index).restrictScalars ℝ).contDiff.comp
        dualSmooth
    exact vectorCoordinateSmooth.mul
      dualCoordinateSmooth
  unfold diracDualScalarYukawaFirstVariationDensity
  exact Complex.reCLM.contDiff.comp complexSmooth

private theorem inputScalarAlgebraic_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeSmooth : ContDiff ℝ ∞ InputActual.coframe :=
    holonomicCoframe_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have coframeAtPoint : InputActual.coframe point = 1 :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have coframeNondegenerate : Matrix.det (InputActual.coframe point) ≠ 0 := by
    rw [coframeAtPoint]
    norm_num
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (InputActual.coframe candidate)|) point :=
    (coframe_volume_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (InputActual.coframe candidate))⁻¹)
      point :=
    (lorentzianMetric_inv_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun candidate =>
        holonomicScalarCovariantDerivative InputActual candidate
          formDirection :=
    holonomicScalarCovariantDerivative_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth formDirection
  have kineticSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        scalarGaugeConnectionKineticFirstVariationDensity
          positiveSmoothUnifiedSource 0 candidate
          (toContinuumPointField InputActual candidate)
          (holonomicScalarVariationAlgebraicDirection InputActual direction
            candidate)) point := by
    unfold scalarGaugeConnectionKineticFirstVariationDensity
      scalarFrameRelativeCovariantDerivative
      holonomicScalarVariationAlgebraicDirection
    simp only [toContinuumPointField,
      scalarFrameRelativeCoordinates_zeroChart]
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro first _
    apply ContDiffAt.sum
    intro second _
    apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
    exact
      ((scalarCoordinatePairingRe_joint_contDiff_local _ _
        (inputScalarVariation_contDiff direction first)
        (covariantSmooth second)).add
        (scalarCoordinatePairingRe_joint_contDiff_local _ _
          (covariantSmooth first)
          (inputScalarVariation_contDiff direction second))).contDiffAt
  have potentialSmooth : ContDiff ℝ ∞ fun candidate =>
      scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField InputActual candidate) direction := by
    unfold scalarPotentialFirstVariation frameRelativeScalarGradient
    exact contDiff_const.mul
      (scalarCoordinatePairingRe_apply_contDiff _ _
        (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.sub
          contDiff_const)
        contDiff_const)
  unfold diracDualScalarAlgebraicDirectionalCoefficient generatedVolumeDensity
  exact volumeSmooth.mul
    ((kineticSmooth.sub potentialSmooth.contDiffAt).add
      (inputScalarYukawa_contDiff direction).contDiffAt)

private theorem inputScalarAlgebraic_zeroSlice_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun space =>
      diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction
        (canonicalCauchySlicePoint 0 space) := by
  rw [contDiff_iff_contDiffAt]
  intro space
  have wholeSlice : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext candidate
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [canonicalCauchySlicePoint, canonicalSpatialInclusion,
          canonicalSpatialCoordinate, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]]
    exact canonicalSpatialInclusion.contDiff
  exact (inputScalarAlgebraic_contDiffAt_zeroSlice space direction).comp
    space wholeSlice.contDiffAt

private theorem inputScalarEuler_zeroSlice_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun space =>
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction
        (canonicalCauchySlicePoint 0 space) := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  exact (inputScalarAlgebraic_zeroSlice_contDiff direction).sub
    (inputScalarDivergence_zeroSlice_contDiff direction)

/-! ## Fixed action provenance and finite coordinate assembly -/

private theorem constitutiveCoframe_eq_input :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe =
      InputActual.coframe := by
  simpa [InputActual] using
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe

private theorem constitutiveGaugeConnection_eq_input :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection =
      InputActual.gaugeConnection := by
  simpa [InputActual] using
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection

private theorem constitutiveScalar_eq_input :
    FixedP506FormNativeConstitutiveJointActionSuccessor.scalar =
      InputActual.scalar := by
  simpa [InputActual] using
    fixedP506FormNativeConstitutiveJointActionSuccessor_scalar

private theorem constitutiveMatter_eq_input :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter =
      InputActual.matter := by
  simpa [InputActual] using
    fixedP506FormNativeConstitutiveJointActionSuccessor_matter

private theorem constitutiveConjugateMatter_eq_input :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter =
      InputActual.conjugateMatter := by
  simpa [InputActual] using
    fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter

private theorem constitutiveScalarCovariantDerivative_eq_input :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor =
      holonomicScalarCovariantDerivative InputActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [constitutiveGaugeConnection_eq_input, constitutiveScalar_eq_input]

private theorem constitutiveScalarMomentum_eq_input
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [constitutiveCoframe_eq_input,
    constitutiveScalarCovariantDerivative_eq_input]

private theorem constitutiveScalarAlgebraic_eq_input
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction =
      diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction := by
  funext point
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    scalarPotentialFirstVariation diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [constitutiveCoframe_eq_input,
    constitutiveGaugeConnection_eq_input,
    constitutiveScalar_eq_input,
    constitutiveScalarCovariantDerivative_eq_input,
    constitutiveMatter_eq_input,
    constitutiveConjugateMatter_eq_input]

private theorem constitutiveScalarEuler_eq_input
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction := by
  funext point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [congrFun (constitutiveScalarAlgebraic_eq_input direction) point]
  simp_rw [constitutiveScalarMomentum_eq_input direction]

private theorem scalarNormalForm_eq_inputEuler
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction
        (canonicalCauchySlicePoint 0 space) := by
  have normal := congrFun
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_zeroSlice_normalForm
      space) direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction
        (canonicalCauchySlicePoint 0 space) = _ at normal
  exact normal.symm.trans
    (congrFun (constitutiveScalarEuler_eq_input direction)
      (canonicalCauchySlicePoint 0 space))

private theorem recenteredContactScalarTemporalDemand_eq_normalForm
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    recenteredContactDiracDualScalarTemporalDemand space direction =
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space direction := by
  have momentumEquality
      (derivativeDirection : LorentzianIndex) :
      scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) direction
          derivativeDirection =
        scalarDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredContactActual space) direction derivativeDirection := by
    have covariantEquality :
        holonomicScalarCovariantDerivative
            (recenteredCartanRepairedConstitutiveCurrent space) =
          holonomicScalarCovariantDerivative (recenteredContactActual space) := by
      funext point formDirection
      unfold holonomicScalarCovariantDerivative
      rw [recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
        recenteredCartanRepairedConstitutiveCurrent_scalar]
    funext point
    unfold scalarDifferentialMomentum
      scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [recenteredCartanRepairedConstitutiveCurrent_coframe,
      covariantEquality]
  have matterOrigin :
      (recenteredCartanRepairedConstitutiveCurrent space).matter 0 =
        (recenteredContactActual space).matter 0 := by
    calc
      (recenteredCartanRepairedConstitutiveCurrent space).matter 0 =
          (fixedP506L0CartanRestartActual space).matter 0 :=
        recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan
          space
      _ =
          (spatiallyRecenterHolonomicConfiguration
            FixedP506FormNativeJointActionSolvedSuccessor space).matter 0 := by
        exact congrFun
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration
              FixedP506FormNativeJointActionSolvedSuccessor space)) 0
      _ = (recenteredContactActual space).matter 0 := by
        unfold recenteredContactActual
        rw [
          diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter]
        unfold diracDualFormNativeRepairedMatterWrittenCurrent
          actionGeneratedDiracDualRepairedMatterJointResponseActual
        rw [
          actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
          actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
  have conjugateOrigin :
      (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter 0 =
        (recenteredContactActual space).conjugateMatter 0 := by
    calc
      (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter 0 =
          (fixedP506L0CartanRestartActual space).conjugateMatter 0 :=
        recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan
          space
      _ =
          (spatiallyRecenterHolonomicConfiguration
            FixedP506FormNativeJointActionSolvedSuccessor space
            ).conjugateMatter 0 := by
        exact congrFun
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration
              FixedP506FormNativeJointActionSolvedSuccessor space)) 0
      _ = (recenteredContactActual space).conjugateMatter 0 := by
        unfold recenteredContactActual
        rw [
          diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter]
        unfold diracDualFormNativeRepairedMatterWrittenCurrent
          actionGeneratedDiracDualRepairedMatterJointResponseActual
        rw [
          actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
        rfl
  have algebraicEquality :
      diracDualScalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) direction 0 =
        diracDualScalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource (recenteredContactActual space)
          direction 0 := by
    unfold diracDualScalarAlgebraicDirectionalCoefficient
      scalarGaugeConnectionKineticFirstVariationDensity
      holonomicScalarVariationAlgebraicDirection
      scalarPotentialFirstVariation diracDualScalarYukawaFirstVariationDensity
      diracDualScalarYukawaVariationVector generatedVolumeDensity
    simp only [toContinuumPointField]
    have covariantEquality :
        holonomicScalarCovariantDerivative
            (recenteredCartanRepairedConstitutiveCurrent space) =
          holonomicScalarCovariantDerivative (recenteredContactActual space) := by
      funext point formDirection
      unfold holonomicScalarCovariantDerivative
      rw [recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
        recenteredCartanRepairedConstitutiveCurrent_scalar]
    rw [recenteredCartanRepairedConstitutiveCurrent_coframe,
      recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
      recenteredCartanRepairedConstitutiveCurrent_scalar,
      covariantEquality,
      matterOrigin, conjugateOrigin]
  have demandAsEuler :
      recenteredContactDiracDualScalarTemporalDemand space direction =
        diracDualScalarEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource (recenteredContactActual space)
          direction 0 := by
    unfold recenteredContactDiracDualScalarTemporalDemand
      recenteredContactDiracDualScalarRequiredPdot
      recenteredContactScalarCurrentPdot
      recenteredContactScalarSpatialMomentumDivergence
    rw [algebraicEquality]
    simp_rw [momentumEquality]
    unfold diracDualScalarEulerLagrangeDirectionalCoefficient
      scalarDifferentialMomentumDivergence
    simp [Fin.sum_univ_four, Fin.sum_univ_three,
      canonicalLorentzianTimeDirection]
    ring
  have contactToNormal :
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          (recenteredContactActual space) 0 =
        recenteredContactJointResidualFullNormalForm space :=
    (recenteredContactJointResidualAtMatchingOccurrence_eq_contactOrigin
      space).symm.trans
      (recenteredContactJointResidualAtMatchingOccurrence_eq_fullNormalForm
        space)
  have contactDirection := congrFun
    (congrArg DiracDualFormNativePointwiseJointResidualCarrier.scalar
      contactToNormal) direction
  simpa only [diracDualFormNativePointwiseJointResidual,
    recenteredContactJointResidualFullNormalForm] using
      demandAsEuler.trans contactDirection

private theorem recenteredContactScalarTemporalDemand_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun space =>
      recenteredContactDiracDualScalarTemporalDemand space direction := by
  rw [show (fun space =>
      recenteredContactDiracDualScalarTemporalDemand space direction) =
    (fun space =>
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource InputActual direction
        (canonicalCauchySlicePoint 0 space)) by
      funext space
      exact
        (recenteredContactScalarTemporalDemand_eq_normalForm space direction).trans
          (scalarNormalForm_eq_inputEuler space direction)]
  exact inputScalarEuler_zeroSlice_contDiff direction

/-- The fixed P506/L0 scalar acceleration generated by the repaired mother
action is a `C∞` function of the matching spatial contact. -/
theorem recenteredContactDiracDualScalarAcceleration_contDiff :
    ContDiff ℝ ∞ recenteredContactDiracDualScalarAcceleration := by
  let assemble : (ScalarBasisIndex → ℂ) →L[ℝ] ScalarCoordinateCarrier :=
    (EuclideanSpace.equiv ScalarBasisIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ fun space index =>
      recenteredContactDiracDualScalarAcceleration space index := by
    apply contDiff_pi'
    intro index
    have realSmooth : ContDiff ℝ ∞ fun space =>
        (recenteredContactDiracDualScalarTemporalDemand space
          (scalarRealBasis index) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp
        (recenteredContactScalarTemporalDemand_contDiff
          (scalarRealBasis index))
    have imaginarySmooth : ContDiff ℝ ∞ fun space =>
        (recenteredContactDiracDualScalarTemporalDemand space
          (scalarImaginaryBasis index) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp
        (recenteredContactScalarTemporalDemand_contDiff
          (scalarImaginaryBasis index))
    change ContDiff ℝ ∞ fun space =>
      -((recenteredContactDiracDualScalarTemporalDemand space
            (scalarRealBasis index) : ℂ) +
        (recenteredContactDiracDualScalarTemporalDemand space
            (scalarImaginaryBasis index) : ℂ) * Complex.I)
    exact (realSmooth.add (imaginarySmooth.mul contDiff_const)).neg
  change ContDiff ℝ ∞ fun space =>
    (EuclideanSpace.equiv ScalarBasisIndex ℂ).symm
      (fun index => recenteredContactDiracDualScalarAcceleration space index)
  exact assemble.contDiff.comp coordinateSmooth

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ScalarAccelerationSpatialRegularity
