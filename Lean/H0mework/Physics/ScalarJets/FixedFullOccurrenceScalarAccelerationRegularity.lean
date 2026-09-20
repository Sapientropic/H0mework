import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.ScalarJets.FixedScalarAccelerationSpatialRegularity
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Fixed P506/L0 full-occurrence scalar-acceleration regularity

The complete-joint mother action recomputes one scalar acceleration at every
four-dimensional occurrence of the fixed P506/L0 current.  This module proves
continuity at the generated common origin directly from the authoritative full
recenter/restart/action chain and the fixed current's local regularity.

The occurrence profile is transported exactly to the scalar Euler coefficient
of the same fixed actual.  No spatial-profile identification, residual value,
target acceleration, branch choice, or regularity receipt is supplied to the
producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance scalarAccelerationMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private theorem genericGeneratedAcceleration_eq_neg_coordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    genericDiracDualScalarGeneratedAcceleration source current =
      -genericDiracDualScalarTemporalDemandCoordinate source current := by
  unfold genericDiracDualScalarGeneratedAcceleration scalarActionRealDual
  congr 1
  apply PiLp.ext
  intro index
  change
    ((genericDiracDualScalarTemporalDemandDual source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarTemporalDemandDual source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I) =
    ((genericDiracDualScalarRawTemporalDemand source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarRawTemporalDemand source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I)
  rw [genericDiracDualScalarTemporalDemandDual_realBasis,
    genericDiracDualScalarTemporalDemandDual_imaginaryBasis]

private theorem genericRawTemporalDemand_eq_scalarEuler_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    genericDiracDualScalarRawTemporalDemand source current direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction 0 := by
  unfold genericDiracDualScalarRawTemporalDemand
    genericDiracDualScalarRequiredPdot genericScalarCurrentPdot
    genericScalarSpatialMomentumDivergence
    diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  simp [Fin.sum_univ_four, Fin.sum_univ_three,
    canonicalLorentzianTimeDirection]
  ring

private theorem completeJointRepaired_matter_origin_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointRepairedConstitutiveCurrent source current).matter 0 =
      current.matter 0 := by
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]

private theorem completeJointRepaired_conjugateMatter_origin_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointRepairedConstitutiveCurrent source current
        ).conjugateMatter 0 =
      current.conjugateMatter 0 := by
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  rfl

private theorem completeJointRepaired_scalarCovariantDerivative_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative
        (completeJointRepairedConstitutiveCurrent source current) =
      holonomicScalarCovariantDerivative current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [completeJointRepairedConstitutiveCurrent_gaugeConnection,
    completeJointRepairedConstitutiveCurrent_scalar]

private theorem completeJointRepaired_scalarMomentum_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (completeJointRepairedConstitutiveCurrent source current)
        direction derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointRepairedConstitutiveCurrent_coframe,
    completeJointRepaired_scalarCovariantDerivative_eq]

private theorem completeJointRepaired_scalarAlgebraic_origin_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current)
        direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient source current
        direction 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointRepairedConstitutiveCurrent_coframe,
    completeJointRepairedConstitutiveCurrent_gaugeConnection,
    completeJointRepairedConstitutiveCurrent_scalar,
    completeJointRepaired_scalarCovariantDerivative_eq,
    completeJointRepaired_matter_origin_eq,
    completeJointRepaired_conjugateMatter_origin_eq]

private theorem completeJointRepaired_scalarEuler_origin_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current)
        direction 0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [completeJointRepaired_scalarAlgebraic_origin_eq]
  simp_rw [completeJointRepaired_scalarMomentum_eq]

private theorem cartanRestart_scalarCovariantDerivative_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) =
      holonomicScalarCovariantDerivative current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]

private theorem cartanRestart_scalarMomentum_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    cartanRestart_scalarCovariantDerivative_eq]

private theorem cartanRestart_scalarAlgebraic_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction =
      diracDualScalarAlgebraicDirectionalCoefficient source current
        direction := by
  funext point
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    cartanRestart_scalarCovariantDerivative_eq,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]

private theorem cartanRestart_scalarEuler_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction := by
  funext point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [congrFun (cartanRestart_scalarAlgebraic_eq source current direction)
    point]
  simp_rw [cartanRestart_scalarMomentum_eq]

private theorem fullOccurrenceRawTemporalDemand_eq_inputScalarEuler
    (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))
        direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction point := by
  rw [genericRawTemporalDemand_eq_scalarEuler_origin,
    completeJointRepaired_scalarEuler_origin_eq]
  unfold completeJointGeneratedProfileRestartCurrent
  rw [congrFun
    (cartanRestart_scalarEuler_eq positiveSmoothUnifiedSource
      (fullyRecenterHolonomicConfiguration FixedInput point) direction) 0]
  have transported :=
    pointwiseJointResidual_fullyRecenter_origin positiveSmoothUnifiedSource
      FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth point
  exact congrFun
    (congrArg
      StageNineDiracDualFormNativeJointResidualCarrier.DiracDualFormNativePointwiseJointResidualCarrier.scalar
      transported)
    direction

/-- Generic action-jet authority seam for the complete-joint scalar profile.
The occurrence restart, repaired constitutive write, and recenter transport
all preserve the scalar Euler read of the same current.  No smoothness,
residual value, or target acceleration is supplied. -/
theorem completeJointScalarRawTemporalDemand_eq_currentScalarEuler
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    genericDiracDualScalarRawTemporalDemand source
        (completeJointRepairedConstitutiveCurrent source
          (completeJointGeneratedProfileRestartCurrent source current point))
        direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        source current direction point := by
  rw [genericRawTemporalDemand_eq_scalarEuler_origin,
    completeJointRepaired_scalarEuler_origin_eq]
  unfold completeJointGeneratedProfileRestartCurrent
  rw [congrFun
    (cartanRestart_scalarEuler_eq source
      (fullyRecenterHolonomicConfiguration current point) direction) 0]
  have transported :=
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      source (fullyRecenterHolonomicConfiguration current point) current
      0 point
      (generatedActionJet_fullyRecenter_origin_unconditional source current
        point)
  exact congrFun
    (congrArg
      StageNineDiracDualFormNativeJointResidualCarrier.DiracDualFormNativePointwiseJointResidualCarrier.scalar
      transported)
    direction

private theorem fixedInput_coframe_origin_eq_one :
    FixedInput.coframe 0 = 1 := by
  rw [FixedInput, fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]
  exact fixedP506JointActual_coframe_origin_one

private theorem fixedInput_scalarMomentum_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource FixedInput
        direction derivativeDirection)
      point := by
  have coframeSmooth : ContDiff ℝ ∞ FixedInput.coframe :=
    holonomicCoframe_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (FixedInput.coframe candidate)|) point :=
    (coframe_volume_contDiffAt
      (FixedInput.coframe point) coframeNondegenerate).comp
        point coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (FixedInput.coframe candidate))⁻¹) point :=
    (lorentzianMetric_inv_contDiffAt
      (FixedInput.coframe point) coframeNondegenerate).comp
        point coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        holonomicScalarCovariantDerivative FixedInput point formDirection) :=
    holonomicScalarCovariantDerivative_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth formDirection
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun _ : BasePoint =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection) :=
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

private theorem fixedInput_scalarMomentumDirectionalDerivative_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource FixedInput
            direction derivativeDirection)
          point derivativeDirection)
      point := by
  unfold fieldDirectionalDerivative
  exact
    ((fixedInput_scalarMomentum_contDiffAt point coframeNondegenerate direction
        derivativeDirection).fderiv_right (by simp)).clm_apply
      contDiffAt_const

private theorem fixedInput_scalarDivergence_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedInput direction)
      point := by
  unfold scalarDifferentialMomentumDivergence
  apply ContDiffAt.sum
  intro derivativeDirection _
  exact
    fixedInput_scalarMomentumDirectionalDerivative_contDiffAt point
      coframeNondegenerate direction derivativeDirection

private def inputWithConstantScalar
    (direction : ScalarCoordinateCarrier) : StageNineHolonomicConfiguration :=
  { FixedInput with scalar := fun _ => direction }

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
        (p286LieBlockEmbed (FixedInput.gaugeConnection point formDirection))
        direction := by
  simpa [inputWithConstantScalar] using
    (holonomicScalarP286Action_contDiff_local
      (inputWithConstantScalar direction)
      (inputWithConstantScalar_smooth direction) formDirection)

private theorem inputScalarYukawaVectorCoordinates_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField FixedInput point) direction) := by
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
          (matterCoordinateEquiv (FixedInput.matter point)))) at actual
  simpa only [diracDualScalarYukawaVariationVector, toContinuumPointField,
    matterCoordinateEquiv.symm_apply_apply] using actual

private theorem inputScalarYukawa_contDiff
    (direction : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ fun point =>
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField FixedInput point) direction := by
  have vectorSmooth := inputScalarYukawaVectorCoordinates_contDiff direction
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (FixedInput.conjugateMatter point) := by
    change ContDiff ℝ ∞
      (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates
        FixedInput)
    exact
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates_contDiff
        FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have complexSmooth : ContDiff ℝ ∞ fun point =>
      FixedInput.conjugateMatter point
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField FixedInput point) direction) := by
    let pairingSum : BasePoint → ℂ := fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField FixedInput point) direction) index *
          matterDualCoordinates (FixedInput.conjugateMatter point) index
    have pairingEquality : (fun point =>
        FixedInput.conjugateMatter point
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField FixedInput point) direction)) =
      pairingSum := by
      funext point
      rw [← matterDualOfCoordinates_surjective
        (FixedInput.conjugateMatter point)]
      exact matterDualOfCoordinates_apply _ _
    rw [pairingEquality]
    unfold pairingSum
    apply ContDiff.sum
    intro index _
    have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField FixedInput point) direction) index := by
      change ContDiff ℝ ∞
        (((EuclideanSpace.proj index).restrictScalars ℝ) ∘
          fun point =>
            matterCoordinateEquiv
              (diracDualScalarYukawaVariationVector
                (toContinuumPointField FixedInput point) direction))
      exact ((EuclideanSpace.proj index).restrictScalars ℝ).contDiff.comp
        vectorSmooth
    have dualCoordinateSmooth : ContDiff ℝ ∞ fun point =>
        matterDualCoordinates (FixedInput.conjugateMatter point) index := by
      change ContDiff ℝ ∞
        (((EuclideanSpace.proj index).restrictScalars ℝ) ∘
          fun point =>
            matterDualCoordinates (FixedInput.conjugateMatter point))
      exact ((EuclideanSpace.proj index).restrictScalars ℝ).contDiff.comp
        dualSmooth
    exact vectorCoordinateSmooth.mul dualCoordinateSmooth
  unfold diracDualScalarYukawaFirstVariationDensity
  exact Complex.reCLM.contDiff.comp complexSmooth

private theorem fixedInput_scalarAlgebraic_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction)
      point := by
  have coframeSmooth : ContDiff ℝ ∞ FixedInput.coframe :=
    holonomicCoframe_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (FixedInput.coframe candidate)|) point :=
    (coframe_volume_contDiffAt
      (FixedInput.coframe point) coframeNondegenerate).comp
        point coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (FixedInput.coframe candidate))⁻¹) point :=
    (lorentzianMetric_inv_contDiffAt
      (FixedInput.coframe point) coframeNondegenerate).comp
        point coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        holonomicScalarCovariantDerivative FixedInput point formDirection :=
    holonomicScalarCovariantDerivative_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth formDirection
  have kineticSmooth : ContDiffAt ℝ ∞
      (fun point =>
        scalarGaugeConnectionKineticFirstVariationDensity
          positiveSmoothUnifiedSource 0 point
          (toContinuumPointField FixedInput point)
          (holonomicScalarVariationAlgebraicDirection FixedInput direction
            point))
      point := by
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
  have potentialSmooth : ContDiff ℝ ∞ fun point =>
      scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField FixedInput point) direction := by
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

private theorem fixedInput_scalarEuler_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction)
      point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  exact
    (fixedInput_scalarAlgebraic_contDiffAt point coframeNondegenerate
      direction).sub
      (fixedInput_scalarDivergence_contDiffAt point coframeNondegenerate
        direction)

private theorem fullOccurrenceRawTemporalDemand_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (fun point =>
        genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
          (completeJointRepairedConstitutiveCurrent
            positiveSmoothUnifiedSource
            (completeJointGeneratedProfileRestartCurrent
              positiveSmoothUnifiedSource FixedInput point))
          direction)
      point := by
  rw [show
    (fun point =>
      genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent
          positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))
        direction) =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction by
    funext point
    exact
      fullOccurrenceRawTemporalDemand_eq_inputScalarEuler point direction]
  exact fixedInput_scalarEuler_contDiffAt point coframeNondegenerate direction

private theorem fullOccurrenceTemporalDemandCoordinate_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (fun point =>
        genericDiracDualScalarTemporalDemandCoordinate
          positiveSmoothUnifiedSource
          (completeJointRepairedConstitutiveCurrent
            positiveSmoothUnifiedSource
            (completeJointGeneratedProfileRestartCurrent
              positiveSmoothUnifiedSource FixedInput point)))
      point := by
  have coordinateSmooth : ContDiffAt ℝ ∞
      (fun point index =>
        (genericDiracDualScalarRawTemporalDemand
            positiveSmoothUnifiedSource
            (completeJointRepairedConstitutiveCurrent
              positiveSmoothUnifiedSource
              (completeJointGeneratedProfileRestartCurrent
                positiveSmoothUnifiedSource FixedInput point))
            (scalarRealBasis index) : ℂ) +
          (genericDiracDualScalarRawTemporalDemand
              positiveSmoothUnifiedSource
              (completeJointRepairedConstitutiveCurrent
                positiveSmoothUnifiedSource
                (completeJointGeneratedProfileRestartCurrent
                  positiveSmoothUnifiedSource FixedInput point))
              (scalarImaginaryBasis index) : ℂ) * Complex.I)
      point := by
    apply contDiffAt_pi'
    intro index
    have realSmooth : ContDiffAt ℝ ∞
        (fun point =>
          (genericDiracDualScalarRawTemporalDemand
              positiveSmoothUnifiedSource
              (completeJointRepairedConstitutiveCurrent
                positiveSmoothUnifiedSource
                (completeJointGeneratedProfileRestartCurrent
                  positiveSmoothUnifiedSource FixedInput point))
              (scalarRealBasis index) : ℂ))
        point := by
      change ContDiffAt ℝ ∞
        (Complex.ofReal ∘ fun point =>
          genericDiracDualScalarRawTemporalDemand
            positiveSmoothUnifiedSource
            (completeJointRepairedConstitutiveCurrent
              positiveSmoothUnifiedSource
              (completeJointGeneratedProfileRestartCurrent
                positiveSmoothUnifiedSource FixedInput point))
            (scalarRealBasis index))
        point
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp
        point
        (fullOccurrenceRawTemporalDemand_contDiffAt point
          coframeNondegenerate (scalarRealBasis index))
    have imaginarySmooth : ContDiffAt ℝ ∞
        (fun point =>
          (genericDiracDualScalarRawTemporalDemand
              positiveSmoothUnifiedSource
              (completeJointRepairedConstitutiveCurrent
                positiveSmoothUnifiedSource
                (completeJointGeneratedProfileRestartCurrent
                  positiveSmoothUnifiedSource FixedInput point))
              (scalarImaginaryBasis index) : ℂ))
        point := by
      change ContDiffAt ℝ ∞
        (Complex.ofReal ∘ fun point =>
          genericDiracDualScalarRawTemporalDemand
            positiveSmoothUnifiedSource
            (completeJointRepairedConstitutiveCurrent
              positiveSmoothUnifiedSource
              (completeJointGeneratedProfileRestartCurrent
                positiveSmoothUnifiedSource FixedInput point))
            (scalarImaginaryBasis index))
        point
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp
        point
        (fullOccurrenceRawTemporalDemand_contDiffAt point
          coframeNondegenerate (scalarImaginaryBasis index))
    exact realSmooth.add (imaginarySmooth.mul contDiffAt_const)
  unfold genericDiracDualScalarTemporalDemandCoordinate
  change ContDiffAt ℝ ∞
    ((EuclideanSpace.equiv ScalarBasisIndex ℂ).symm ∘ fun point =>
      (fun index =>
        (genericDiracDualScalarRawTemporalDemand
            positiveSmoothUnifiedSource
            (completeJointRepairedConstitutiveCurrent
              positiveSmoothUnifiedSource
              (completeJointGeneratedProfileRestartCurrent
                positiveSmoothUnifiedSource FixedInput point))
            (scalarRealBasis index) : ℂ) +
          (genericDiracDualScalarRawTemporalDemand
              positiveSmoothUnifiedSource
              (completeJointRepairedConstitutiveCurrent
                positiveSmoothUnifiedSource
                (completeJointGeneratedProfileRestartCurrent
                  positiveSmoothUnifiedSource FixedInput point))
              (scalarImaginaryBasis index) : ℂ) * Complex.I))
    point
  let reconstruct :
      (ScalarBasisIndex → ℂ) →L[ℝ] ScalarCoordinateCarrier :=
    (EuclideanSpace.equiv ScalarBasisIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  exact reconstruct.contDiff.contDiffAt.comp point coordinateSmooth

private theorem fullOccurrenceGeneratedAcceleration_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (FixedInput.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (fun point =>
        genericDiracDualScalarGeneratedAcceleration
          positiveSmoothUnifiedSource
          (completeJointRepairedConstitutiveCurrent
            positiveSmoothUnifiedSource
            (completeJointGeneratedProfileRestartCurrent
              positiveSmoothUnifiedSource FixedInput point)))
      point := by
  rw [show
    (fun point =>
      genericDiracDualScalarGeneratedAcceleration
        positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent
          positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))) =
      fun point =>
        -genericDiracDualScalarTemporalDemandCoordinate
          positiveSmoothUnifiedSource
          (completeJointRepairedConstitutiveCurrent
            positiveSmoothUnifiedSource
            (completeJointGeneratedProfileRestartCurrent
              positiveSmoothUnifiedSource FixedInput point)) by
    funext point
    exact genericGeneratedAcceleration_eq_neg_coordinate _ _]
  exact
    (fullOccurrenceTemporalDemandCoordinate_contDiffAt point
      coframeNondegenerate).neg

/-- At every nondegenerate occurrence, the fixed source/current action
generates a locally smooth scalar-acceleration profile.  Nondegeneracy is a
domain condition for the already generated action read; no acceleration,
residual, or target jet is supplied. -/
theorem fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt
    (point : BasePoint)
    (coframeNondegenerate :
      Matrix.det
          (FixedP506FormNativeJointActionSolvedSuccessor.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      point := by
  unfold completeJointScalarAccelerationProfile
  change ContDiffAt ℝ ∞
    (fun point =>
      genericDiracDualScalarGeneratedAcceleration positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point)))
    point
  exact
    fullOccurrenceGeneratedAcceleration_contDiffAt point
      coframeNondegenerate

/-- Every fixed P506/L0 occurrence on the canonical zero slice lies in the
nondegenerate action domain, so the generated acceleration profile is smooth
there without an additional regularity receipt. -/
theorem fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      (canonicalCauchySlicePoint 0 space) := by
  apply fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
  norm_num

/-- The common origin is a nondegenerate specialization of the generated
occurrence-local regularity theorem. -/
theorem fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      0 := by
  apply fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt
  rw [fixedInput_coframe_origin_eq_one]
  norm_num

/-- Compatibility readout: the generated fixed scalar acceleration is
continuous at the common origin. -/
theorem fixedP506L0CompleteJointScalarAccelerationProfile_continuousAt_origin :
    ContinuousAt
      (completeJointScalarAccelerationProfile
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      0 :=
  fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin.continuousAt

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
