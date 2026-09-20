import H0mework.Physics.JointVariation.P286LiveElectricCauchyOperator
import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286OriginMagneticCompatibility
import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286ZeroSliceContinuity
import H0mework.Physics.FixedJoint.FixedJointP286RequiredExteriorProfileRegularity

/-!
# Fixed P506/L0 complete-joint P286 live-electric Cauchy operator

This module specializes the source/current-only live-electric Cauchy
operator to the fixed P506/L0 lineage.  It contains fixed-field
identifications and the conditional analytic readout seam; the producer
itself remains in the imported generic module.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286LiveElectricCauchyOperator

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalRestrictionP286CoherentRegularity
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286OriginMagneticCompatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceCompatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceContinuity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionVariation
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286HolonomicSecondJetCarrier
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Interval Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fullOccurrenceGlobalJetP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fullOccurrenceGlobalJetP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance fullOccurrenceGlobalJetP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

/-! ## Fixed P506/L0 specialization -/

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedTemporalCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource FixedInput

private abbrev FixedAlgebraicBase : StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate FixedTemporalCurrent
    (diracDualFormNativeP286CanonicalGeneratedWrite
      positiveSmoothUnifiedSource FixedTemporalCurrent)

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedLiveElectricCauchyCurrent :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- For the fixed constitutive current, the live-electric base carries the
literal full algebraic value on the entire zero slice. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    completeJointP286LiveElectricZeroSliceMagneticBase_coordinate]
  unfold completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
  rw [completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor]
  funext pair
  fin_cases pair <;>
    simp [p286ElectricProjection, p286MagneticProjection]

/-- The full action-owned producer therefore has the same exact Cauchy
boundary, including all electric and magnetic coordinates. -/
theorem fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate FixedLiveElectricCauchyCurrent
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_zeroSlice,
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_zeroSlice]

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_origin :
    holonomicP286GaugeAuxiliaryCoordinate FixedLiveElectricCauchyCurrent 0 =
      holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent 0 := by
  simpa [canonicalCauchySlicePoint_zero_zero_local] using
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_zeroSlice 0

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_gaugeAuxiliary_origin :
    FixedLiveElectricCauchyCurrent.gaugeAuxiliary 0 =
      FixedAlgebraicCurrent.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_origin
    pair

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_pointField_origin :
    toContinuumPointField FixedLiveElectricCauchyCurrent 0 =
      toContinuumPointField FixedAlgebraicCurrent 0 := by
  apply StageNineContinuumPointField.ext <;> try rfl
  exact
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_gaugeAuxiliary_origin

/-- The action target consumed by the temporal producer is also the direct
connection-action target of its own output at the fixed occurrence. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_requiredExterior_origin :
    completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 =
      formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent := by
  rw [
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct]
  unfold formNativeCurrentP286RequiredExteriorDerivative
  rw [
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_pointField_origin]
  rw [show
    holonomicP286GaugeConnectionCoordinate FixedLiveElectricCauchyCurrent 0 =
      holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent 0 by
        rfl]
  rw [
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_origin]

private abbrev FixedCanonicalRegularityInput :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev FixedCanonicalRegularityConnection :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private abbrev FixedCanonicalRegularityActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev FixedZeroSliceAnchor :
    StageNineHolonomicConfiguration :=
  completeJointP286ZeroSliceAnchoredCurrent positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private theorem fixedCanonicalRegularityConnection_smooth :
    FixedCanonicalRegularityConnection.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth
    FixedCanonicalRegularityInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite) 1

private theorem
    fixedCanonicalRegularityCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeCurvatureCoordinate
        FixedCanonicalRegularityConnection) := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff
      FixedCanonicalRegularityConnection
      fixedCanonicalRegularityConnection_smooth pair)

private theorem fixedCanonicalRegularityAuxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate
        FixedCanonicalRegularityActual) 0 := by
  have nondegenerate :
      Matrix.det (FixedCanonicalRegularityInput.coframe 0) ≠ 0 := by
    change
      Matrix.det
        (fixedP506L0P286CanonicalGeneratedActual.coframe 0) ≠ 0
    rw [fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
    norm_num
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedCanonicalRegularityInput.coframe 0) nondegenerate
      (holonomicP286GaugeCurvatureCoordinate
        FixedCanonicalRegularityConnection 0)
  have inner : ContDiffAt ℝ ∞
      (fun point =>
        (FixedCanonicalRegularityInput.coframe point,
          holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalRegularityConnection point)) 0 :=
    (holonomicCoframe_contDiff FixedCanonicalRegularityInput
      (fixedP506L0FinalCommonActionActual_smooth 0)).contDiffAt.prodMk
        fixedCanonicalRegularityCurvatureCoordinate_contDiff.contDiffAt
  have composed := outer.comp 0 inner
  have coordinateEq :
    holonomicP286GaugeAuxiliaryCoordinate
        FixedCanonicalRegularityActual =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (FixedCanonicalRegularityInput.coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalRegularityConnection point) := by
    funext point
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliary]
    change
      formNativeP286GaugeActualToCoordinateLinear
          (StageNineFormNativeP286GaugeConstitutiveElimination.formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
            (FixedCanonicalRegularityInput.coframe point)
            (holonomicGaugeCurvature
              FixedCanonicalRegularityConnection point)) =
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (FixedCanonicalRegularityInput.coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            FixedCanonicalRegularityConnection point)
    unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    rw [show
      holonomicP286GaugeCurvatureCoordinate
          FixedCanonicalRegularityConnection point =
        formNativeP286GaugeActualToCoordinateLinear
          (holonomicGaugeCurvature
            FixedCanonicalRegularityConnection point) by
        rfl]
    rw [formNativeP286GaugeActual_coordinate_actual]
  rw [coordinateEq]
  exact composed

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]
  exact fixedCanonicalRegularityAuxiliaryCoordinate_contDiffAt_origin

private theorem
    fixedP506L0CompleteJointP286ZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedZeroSliceAnchor) 0 := by
  rw [
    fixedP506L0CompleteJointP286ZeroSliceAnchor_coordinate_eq_pullback]
  have algebraicAtProjection : ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
      (canonicalRestrictionZeroSliceProjection 0) := by
    rw [canonicalRestrictionZeroSliceProjection.map_zero]
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_contDiffAt_origin
  exact ContDiffAt.comp
    (g := holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
    (f := fun point : BasePoint =>
      canonicalRestrictionZeroSliceProjection point)
    0 algebraicAtProjection
    canonicalRestrictionZeroSliceProjection.contDiff.contDiffAt

private theorem
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)) 0 := by
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent) =
      completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
        positiveSmoothUnifiedSource FixedAlgebraicCurrent by
      funext point
      exact
        completeJointP286LiveElectricZeroSliceMagneticBase_coordinate
          positiveSmoothUnifiedSource FixedAlgebraicCurrent point]
  apply contDiffAt_pi.mpr
  intro pair
  fin_cases pair
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_contDiffAt_origin
        0)
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_contDiffAt_origin
        1)
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_contDiffAt_origin
        2)
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection,
      completeJointP286ZeroSliceAnchoredCurrent,
      holonomicP286GaugeAuxiliaryCoordinate] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointP286ZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin
        3)
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection,
      completeJointP286ZeroSliceAnchoredCurrent,
      holonomicP286GaugeAuxiliaryCoordinate] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointP286ZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin
        4)
  · simpa [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection,
      completeJointP286ZeroSliceAnchoredCurrent,
      holonomicP286GaugeAuxiliaryCoordinate] using
      (contDiffAt_pi.mp
        fixedP506L0CompleteJointP286ZeroSliceAnchor_auxiliaryCoordinate_contDiffAt_origin
        5)

/-- The fixed live-electric Cauchy base is differentiable at the common
occurrence: its electric coordinates come from the algebraic current and its
magnetic coordinates from the established zero-slice anchor. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent))
      0 := by
  exact
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_contDiffAt_origin.differentiableAt
      (by simp)

private theorem
    holonomicP286GaugeAuxiliaryExteriorDerivative_contDiffAt_of_coordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinateRegular :
      ContDiffAt ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate configuration) point) :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative configuration) point := by
  have firstJetRegular : ContDiffAt ℝ ∞
      (fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate configuration)) point :=
    coordinateRegular.fderiv_right (by simp)
  have directionalRegular
      (direction : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286GaugeAuxiliaryDirectionalDerivative
            configuration candidate direction) point := by
    unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    exact firstJetRegular.clm_apply contDiffAt_const
  have orderedRegular
      (direction first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun candidate =>
          orderedP286GaugeTwoFormComponent
            (p286GaugeAuxiliaryDirectionalDerivative
              configuration candidate direction)
            first second) point := by
    unfold orderedP286GaugeTwoFormComponent
    apply ContDiffAt.sum
    intro pair _
    have coefficientRegular : ContDiffAt ℝ ∞
        (fun _ : BasePoint =>
          orientedLorentzBivectorBasisCoefficient pair first second)
        point :=
      contDiffAt_const
    exact coefficientRegular.smul
      (contDiffAt_pi.mp (directionalRegular direction) pair)
  apply contDiffAt_pi.mpr
  intro triple
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
  exact
    ((orderedRegular (threeFormFirst triple) (threeFormSecond triple)
        (threeFormThird triple)).add
      (orderedRegular (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (orderedRegular (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

theorem
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_exteriorDerivative_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)) 0 :=
  holonomicP286GaugeAuxiliaryExteriorDerivative_contDiffAt_of_coordinate
    (completeJointP286LiveElectricZeroSliceMagneticBase
      positiveSmoothUnifiedSource FixedAlgebraicCurrent)
    0
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_contDiffAt_origin

private def liveElectricTemporalWriteLinear :
    P286GaugeThreeForm →ₗ[ℝ] P286GaugeTwoForm where
  toFun := fun target =>
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target
      canonicalLorentzianTimeDirection
  map_add' := by
    intro first second
    funext pair
    fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
        canonicalLorentzianTimeDirection]
    all_goals module
  map_smul' := by
    intro parameter target
    funext pair
    fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
        canonicalLorentzianTimeDirection]

private def liveElectricTemporalWriteCLM :
    P286GaugeThreeForm →L[ℝ] P286GaugeTwoForm :=
  liveElectricTemporalWriteLinear.toContinuousLinearMap

/-- The complete action-owned temporal profile is continuous at the fixed
occurrence.  This combines the already established local mother-action
profile with the explicit smooth live-electric Cauchy base. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_continuousAt_origin :
    ContinuousAt
      (completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent) 0 := by
  have differenceContinuous :
      ContinuousAt
        (fun point =>
          completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point)
        0 :=
    fixedP506L0CompleteJointP286RequiredExteriorProfile_continuousAt_origin.sub
      fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_exteriorDerivative_contDiffAt_origin.continuousAt
  rw [show
    completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent =
      fun point =>
        liveElectricTemporalWriteCLM
          (completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point) by
      rfl]
  exact liveElectricTemporalWriteCLM.continuous.continuousAt.comp'
    differenceContinuous

private theorem canonicalCauchyTimeLine_zero_contDiff :
    ContDiff ℝ ∞
      (fun candidateTime : ℝ =>
        canonicalCauchySlicePoint candidateTime
          (0 : StageNineSpatialPoint)) := by
  apply contDiff_piLp'
  intro direction
  fin_cases direction
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three, Function.id_def] using
      (contDiff_id : ContDiff ℝ ∞ (fun candidateTime : ℝ => candidateTime))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_continuousAt_origin
    (pair : Fin 6) :
    ContinuousAt
      (fun candidateTime =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent
          (canonicalCauchySlicePoint candidateTime 0) pair)
      0 := by
  have outerAtOrigin :=
    continuousAt_pi.mp
      fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_continuousAt_origin
      pair
  have composed :=
    outerAtOrigin.comp_of_eq
      canonicalCauchyTimeLine_zero_contDiff.continuous.continuousAt
      canonicalCauchySlicePoint_zero_zero_local
  convert composed using 1
  funext candidateTime
  rfl

private theorem
    holonomicP286GaugeAuxiliaryExteriorDerivative_stronglyMeasurable
    (configuration : StageNineHolonomicConfiguration) :
    StronglyMeasurable
      (holonomicP286GaugeAuxiliaryExteriorDerivative configuration) := by
  have derivativeMeasurable :
      StronglyMeasurable
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate configuration)) :=
    (measurable_fderiv ℝ
      (holonomicP286GaugeAuxiliaryCoordinate configuration)
      ).stronglyMeasurable
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    fieldDirectionalDerivative
    orderedP286GaugeTwoFormComponent
  apply Measurable.stronglyMeasurable
  apply measurable_pi_iff.mpr
  intro triple
  fun_prop

theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_stronglyMeasurable_of_required
    (requiredMeasurable :
      StronglyMeasurable
        (completeJointP286RequiredExteriorProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)) :
    StronglyMeasurable
      (completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent) := by
  have differenceMeasurable :
      StronglyMeasurable
        (fun point =>
          completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point) :=
    requiredMeasurable.sub
      (holonomicP286GaugeAuxiliaryExteriorDerivative_stronglyMeasurable
        (completeJointP286LiveElectricZeroSliceMagneticBase
          positiveSmoothUnifiedSource FixedAlgebraicCurrent))
  rw [show
    completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent =
      fun point =>
        liveElectricTemporalWriteCLM
          (completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point) by
      rfl]
  exact
    liveElectricTemporalWriteCLM.continuous.stronglyMeasurable
      |>.comp_measurable differenceMeasurable.measurable

theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_of_required
    (requiredMeasurable :
      StronglyMeasurable
        (completeJointP286RequiredExteriorProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent))
    (pair : Fin 6) :
    StronglyMeasurableAtFilter
      (fun candidateTime =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent
          (canonicalCauchySlicePoint candidateTime 0) pair)
      (nhds 0) MeasureTheory.volume := by
  have profileMeasurable :=
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_stronglyMeasurable_of_required
      requiredMeasurable
  have evaluationMeasurable :
      StronglyMeasurable
        (fun point =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair) :=
    (continuous_apply pair).stronglyMeasurable.comp_measurable
      profileMeasurable.measurable
  have timeLineMeasurable :
      Measurable
        (fun candidateTime : ℝ =>
          canonicalCauchySlicePoint candidateTime
            (0 : StageNineSpatialPoint)) :=
    canonicalCauchyTimeLine_zero_contDiff.continuous.measurable
  exact
    (evaluationMeasurable.comp_measurable timeLineMeasurable
      ).stronglyMeasurableAtFilter

theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_contDiffAt_origin_of_required
    (requiredRegular :
      ContDiffAt ℝ 0
        (completeJointP286RequiredExteriorProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0) :
    ContDiffAt ℝ 0
      (completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent)
      0 := by
  have differenceRegular :
      ContDiffAt ℝ 0
        (fun point =>
          completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point)
        0 :=
    requiredRegular.sub
      (fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_exteriorDerivative_contDiffAt_origin.of_le
        (by simp))
  rw [show
    completeJointP286LiveElectricActionTemporalWriteProfile
        positiveSmoothUnifiedSource FixedAlgebraicCurrent =
      fun point =>
        liveElectricTemporalWriteCLM
          (completeJointP286RequiredExteriorProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point -
            holonomicP286GaugeAuxiliaryExteriorDerivative
              (completeJointP286LiveElectricZeroSliceMagneticBase
                positiveSmoothUnifiedSource FixedAlgebraicCurrent)
              point) by
      rfl]
  exact liveElectricTemporalWriteCLM.contDiff.contDiffAt.comp
    0 differenceRegular

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_of_profile
    (profileRegular :
      ContDiffAt ℝ 0
        (completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate
        FixedLiveElectricCauchyCurrent)
      0 := by
  have primitiveDifferentiable :
      DifferentiableAt ℝ
        (completeJointP286LiveElectricActionTemporalWritePrimitive
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0 := by
    apply differentiableAt_pi.mpr
    intro pair
    change
      DifferentiableAt ℝ
        (canonicalTimePrimitive
          (fun point =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair))
        0
    exact
      (canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
        (fun point =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair)
        (contDiffAt_pi.mp profileRegular pair)).differentiableAt
  have coordinateEq :
    holonomicP286GaugeAuxiliaryCoordinate FixedLiveElectricCauchyCurrent =
      holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            positiveSmoothUnifiedSource FixedAlgebraicCurrent) +
        completeJointP286LiveElectricActionTemporalWritePrimitive
          positiveSmoothUnifiedSource FixedAlgebraicCurrent := by
    funext point
    rw [
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate,
      ← completeJointP286LiveElectricZeroSliceMagneticBase_coordinate]
    simp only [Pi.add_apply]
  rw [coordinateEq]
  exact
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_differentiableAt_origin.add
      primitiveDifferentiable

theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_of_contDiffAt
    (profileRegular :
      ContDiffAt ℝ 0
        (completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0)
    (pair : Fin 6) :
    StronglyMeasurableAtFilter
      (fun candidateTime =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent
          (canonicalCauchySlicePoint candidateTime 0) pair)
      (nhds 0) MeasureTheory.volume := by
  have coordinateAtOrigin :=
    contDiffAt_pi.mp profileRegular pair
  have timeLineRegular :
      ContDiffAt ℝ 0
        (fun candidateTime : ℝ =>
          canonicalCauchySlicePoint candidateTime
            (0 : StageNineSpatialPoint))
        0 :=
    canonicalCauchyTimeLine_zero_contDiff.contDiffAt.of_le (by simp)
  have coordinateAtTimeLineOrigin :
      ContDiffAt ℝ 0
        (fun point =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair)
        ((fun candidateTime : ℝ =>
          canonicalCauchySlicePoint candidateTime
            (0 : StageNineSpatialPoint)) 0) := by
    change
      ContDiffAt ℝ 0
        (fun point =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair)
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
    rw [canonicalCauchySlicePoint_zero_zero_local]
    exact coordinateAtOrigin
  have lineRegular :
      ContDiffAt ℝ 0
        (fun candidateTime : ℝ =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent
            (canonicalCauchySlicePoint candidateTime 0) pair)
        0 :=
    ContDiffAt.comp
      (f := fun candidateTime : ℝ =>
        canonicalCauchySlicePoint candidateTime
          (0 : StageNineSpatialPoint))
      (g := fun point =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent point pair)
      0 coordinateAtTimeLineOrigin timeLineRegular
  obtain ⟨localSet, localSetNhd, lineContinuousOn⟩ :=
    contDiffAt_zero.mp lineRegular
  obtain ⟨openSet, openSetSubset, openSetOpen, originInOpenSet⟩ :=
    mem_nhds_iff.mp localSetNhd
  exact
    ContinuousOn.stronglyMeasurableAtFilter openSetOpen
      (lineContinuousOn.mono openSetSubset)
      0 originInOpenSet

/-- Spatial derivatives at the fixed occurrence are inherited from the same
algebraic current.  The only analytic premise is differentiability of the
newly generated whole field at that occurrence. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_spatialDirectionalDerivative_origin
    (direction : Fin 3)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent) 0) :
    p286GaugeAuxiliaryDirectionalDerivative
        FixedLiveElectricCauchyCurrent 0 direction.succ =
      p286GaugeAuxiliaryDirectionalDerivative
        FixedAlgebraicCurrent 0 direction.succ := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate FixedLiveElectricCauchyCurrent
  let algebraicCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent
  have finalAtSlice :
      DifferentiableAt ℝ finalCoordinate
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero_local]
    exact finalCoordinateDifferentiableAt
  have algebraicAtSlice :
      DifferentiableAt ℝ algebraicCoordinate
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero_local]
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_differentiableAt_origin
  rw [show (0 : BasePoint) =
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) by
        exact canonicalCauchySlicePoint_zero_zero_local.symm]
  change
    fieldDirectionalDerivative finalCoordinate
        (canonicalCauchySlicePoint 0 0) direction.succ =
      fieldDirectionalDerivative algebraicCoordinate
        (canonicalCauchySlicePoint 0 0) direction.succ
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local finalCoordinate
      0 0 direction finalAtSlice,
    ← fderiv_canonicalCauchySlicePoint_spatial_local algebraicCoordinate
      0 0 direction algebraicAtSlice]
  have sliceEquality :
      finalCoordinate ∘ canonicalCauchySlicePoint 0 =
        algebraicCoordinate ∘ canonicalCauchySlicePoint 0 := by
    funext space
    exact
      fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_zeroSlice space
  rw [sliceEquality]

/-- The remaining spatial `123` coordinate is already the authoritative
fixed P506/L0 action read on the same generated actual. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin_three
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent) 0) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedLiveElectricCauchyCurrent 0 3 =
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 3 := by
  calc
    holonomicP286GaugeAuxiliaryExteriorDerivative
          FixedLiveElectricCauchyCurrent 0 3 =
        holonomicP286GaugeAuxiliaryExteriorDerivative
          FixedAlgebraicCurrent 0 3 := by
      simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
        threeFormFirst, threeFormSecond, threeFormThird,
        orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
        orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
      have first :
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedLiveElectricCauchyCurrent 0 1) 3 =
            (p286GaugeAuxiliaryDirectionalDerivative
              FixedAlgebraicCurrent 0 1) 3 := by
        simpa using congrFun
          (fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_spatialDirectionalDerivative_origin
            0 finalCoordinateDifferentiableAt) 3
      have second :
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedLiveElectricCauchyCurrent 0 2) 4 =
            (p286GaugeAuxiliaryDirectionalDerivative
              FixedAlgebraicCurrent 0 2) 4 := by
        simpa using congrFun
          (fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_spatialDirectionalDerivative_origin
            1 finalCoordinateDifferentiableAt) 4
      have third :
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedLiveElectricCauchyCurrent 0 3) 5 =
            (p286GaugeAuxiliaryDirectionalDerivative
              FixedAlgebraicCurrent 0 3) 5 := by
        simpa using congrFun
          (fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_spatialDirectionalDerivative_origin
            2 finalCoordinateDifferentiableAt) 5
      rw [first, second, third]
    _ =
        completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
          FixedAlgebraicCurrent 0 3 := by
      rw [
        fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct,
        ←
          fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_origin_eq_required]

/-- All four pure-exterior coordinates close simultaneously at the fixed
occurrence.  The only remaining premises validate the generated primitive;
the Cauchy base and endpoint continuity are now discharged from the explicit
fixed normal form. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent) 0)
    (profileMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent
              (canonicalCauchySlicePoint candidateTime 0) pair)
          (nhds 0) MeasureTheory.volume) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedLiveElectricCauchyCurrent 0 =
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 := by
  have finalAtSlice :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent)
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero_local]
    exact finalCoordinateDifferentiableAt
  have baseAtSlice :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            positiveSmoothUnifiedSource FixedAlgebraicCurrent))
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero_local]
    exact
      fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_differentiableAt_origin
  have profileIntervalIntegrable
      (pair : Fin 6) :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            positiveSmoothUnifiedSource FixedAlgebraicCurrent
            (canonicalCauchySlicePoint candidateTime 0) pair)
        MeasureTheory.volume 0 0 := by
    simp
  funext triple
  fin_cases triple
  · simpa [canonicalCauchySlicePoint_zero_zero_local] using
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_exteriorDerivative_temporal
        positiveSmoothUnifiedSource FixedAlgebraicCurrent 0 0 0
        (by decide) finalAtSlice baseAtSlice
        profileIntervalIntegrable profileMeasurableAt
        fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_continuousAt_origin
  · simpa [canonicalCauchySlicePoint_zero_zero_local] using
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_exteriorDerivative_temporal
        positiveSmoothUnifiedSource FixedAlgebraicCurrent 0 0 1
        (by decide) finalAtSlice baseAtSlice
        profileIntervalIntegrable profileMeasurableAt
        fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_continuousAt_origin
  · simpa [canonicalCauchySlicePoint_zero_zero_local] using
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_exteriorDerivative_temporal
        positiveSmoothUnifiedSource FixedAlgebraicCurrent 0 0 2
        (by decide) finalAtSlice baseAtSlice
        profileIntervalIntegrable profileMeasurableAt
        fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_continuousAt_origin
  · exact
      fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin_three
        finalCoordinateDifferentiableAt

/-- Producer soundness for the complete fixed P506/L0 P286 connection
equation on the same generated output actual. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent) 0)
    (profileMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              positiveSmoothUnifiedSource FixedAlgebraicCurrent
              (canonicalCauchySlicePoint candidateTime 0) pair)
          (nhds 0) MeasureTheory.volume) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedLiveElectricCauchyCurrent 0 =
      0 := by
  rw [holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current]
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin
      finalCoordinateDifferentiableAt profileMeasurableAt,
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_requiredExterior_origin]
  unfold formNativeCurrentP286RequiredExteriorDerivative
  abel

/-- One local-regularity mouth now discharges the complete fixed
connection equation.  The premise concerns the authoritative action read,
not a target field, residual coordinate, or equation certificate. -/
theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin_of_required
    (requiredRegular :
      ContDiffAt ℝ 0
        (completeJointP286RequiredExteriorProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedLiveElectricCauchyCurrent 0 =
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 := by
  have profileRegular :=
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_contDiffAt_origin_of_required
      requiredRegular
  exact
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin
      (fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_of_profile
        profileRegular)
      (fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_of_contDiffAt
        profileRegular)

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin_of_required
    (requiredRegular :
      ContDiffAt ℝ 0
        (completeJointP286RequiredExteriorProfile
          positiveSmoothUnifiedSource FixedAlgebraicCurrent)
        0) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedLiveElectricCauchyCurrent 0 =
      0 := by
  have profileRegular :=
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_contDiffAt_origin_of_required
      requiredRegular
  exact
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin
      (fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_of_profile
        profileRegular)
      (fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_of_contDiffAt
        profileRegular)

theorem fixedP506L0CompleteJointP286FullOccurrenceGlobalActionJet
    (point : BasePoint) :
    completeJointP286FullOccurrenceGlobalActionJet
        positiveSmoothUnifiedSource FixedAlgebraicCurrent point =
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent point,
        pointwiseDirectP286RequiredExteriorDerivative
          positiveSmoothUnifiedSource FixedAlgebraicCurrent point) := by
  change
    completeJointP286FullOccurrenceGlobalActionJet
        positiveSmoothUnifiedSource
        (formNativeP286GaugeConstitutiveReadout
          positiveSmoothUnifiedSource FixedAlgebraicBase) point =
      _
  exact
    completeJointP286FullOccurrenceGlobalActionJet_constitutiveReadout
      positiveSmoothUnifiedSource FixedAlgebraicBase point

theorem
    fixedP506L0CompleteJointP286FullOccurrenceGlobalAuxiliaryOperator_gaugeAuxiliary :
    (completeJointP286FullOccurrenceGlobalAuxiliaryOperator
      positiveSmoothUnifiedSource FixedAlgebraicCurrent).gaugeAuxiliary =
      FixedAlgebraicCurrent.gaugeAuxiliary := by
  change
    (completeJointP286FullOccurrenceGlobalAuxiliaryOperator
      positiveSmoothUnifiedSource
      (formNativeP286GaugeConstitutiveReadout
        positiveSmoothUnifiedSource FixedAlgebraicBase)).gaugeAuxiliary =
      _
  exact
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator_gaugeAuxiliary_constitutiveReadout
      positiveSmoothUnifiedSource FixedAlgebraicBase

theorem
    fixedP506L0CompleteJointP286FullOccurrenceGlobalAuxiliaryOperator_eq :
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator
        positiveSmoothUnifiedSource FixedAlgebraicCurrent =
      FixedAlgebraicCurrent := by
  change
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator
        positiveSmoothUnifiedSource
        (formNativeP286GaugeConstitutiveReadout
          positiveSmoothUnifiedSource FixedAlgebraicBase) =
      _
  exact
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator_constitutiveReadout
      positiveSmoothUnifiedSource FixedAlgebraicBase

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286LiveElectricCauchyOperator
