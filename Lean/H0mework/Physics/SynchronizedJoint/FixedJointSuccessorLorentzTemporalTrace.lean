import H0mework.Physics.SynchronizedJoint.FixedCoupledTemporalOriginProfileZero
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorStructuralReduction
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointZeroSlice
import H0mework.Physics.IdentityGerms.IdentityECCartanRestartOriginFirstGerm

/-!
# Fixed P506 action-selected successor temporal Lorentz trace

The action-selected temporal producer gives zero primal and adjoint velocity
at the fixed P506/L0 origin.  This module transports those two generated
profile laws through the finite W13 pairing and the no-choice Cartan
torsion--contorsion equivalence.  Because the same coupled actual carries the
global identity coframe, both connection components used by the faithful
Lorentz trace have zero temporal first jet.

This is a primitive-profile transporter and a post-write readout of the
already generated common successor.  It accepts no residual, support,
target derivative, correction, branch, or completion receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedJointSuccessorLorentzTemporalTrace

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedCoupledTemporalOriginProfileZero
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
open StageNineDiracKineticLocalSpinMaurerCalculus
open StageNineDiracMatterCoordinateCalculus
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open StageNineTopologicalLorentzThreeFormDuality

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance actionSelectedTraceMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Radial : StageNineHolonomicConfiguration :=
  completeJointActionSelectedRadialConnectionActual Source Current

private abbrev Constitutive : StageNineHolonomicConfiguration :=
  completeJointActionSelectedRadialConstitutiveActual Source Current

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private abbrev Cartan : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source Coupled

theorem fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one :
    Coupled.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Coupled.coframe = Carry.coframe :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry
    _ = Constitutive.coframe :=
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_coframe
        Source Current Constitutive
    _ = Radial.coframe := rfl
    _ = Current.coframe := rfl
    _ = fun _ => (1 : LorentzianCoframe) :=
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one

private theorem coupled_matterCoordinates_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        0 canonicalLorentzianTimeDirection = 0 := by
  have derivative :=
    actionSelectedCoupled_matterTemporalDerivative_zeroSlice
      (space := (0 : StageNineSpatialPoint))
  rw [canonicalCauchySlicePoint_zero_zero,
    fixedP506L0ActionSelectedCoupledTemporalProfile_matterVelocity_zero]
      at derivative
  simpa using derivative

private theorem coupled_conjugateMatterCoordinates_temporalDerivative_zero :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Coupled)
        0 canonicalLorentzianTimeDirection = 0 := by
  have derivative :=
    actionSelectedCoupled_conjugateMatterTemporalDerivative_zeroSlice
      (space := (0 : StageNineSpatialPoint))
  rw [canonicalCauchySlicePoint_zero_zero,
    fixedP506L0ActionSelectedCoupledTemporalProfile_adjointVelocity_zero]
      at derivative
  simpa using derivative

private def SpinVector
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (point : BasePoint) : MatterCoordinateCarrier :=
  lorentzSpinCoordinateLinear variationDirection internalPair
    (matterCoordinateEquiv (Coupled.matter point))

private def DualVector (point : BasePoint) : MatterCoordinateCarrier :=
  holonomicConjugateMatterCoordinates Coupled point

private theorem spinVector_contDiff
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞ (SpinVector variationDirection internalPair) := by
  apply
    (lorentzSpinCoordinateLinear variationDirection internalPair).contDiff.comp
  exact actionSelectedCoupled_matterCoordinates_contDiff

private theorem dualVector_contDiff : ContDiff ℝ ∞ DualVector :=
  actionSelectedCoupled_conjugateMatterCoordinates_contDiff

private theorem spinVector_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (SpinVector variationDirection internalPair)
        0 canonicalLorentzianTimeDirection = 0 := by
  unfold SpinVector
  rw [fieldDirectionalDerivative_continuousLinear
    (lorentzSpinCoordinateLinear variationDirection internalPair)
    (fun point => matterCoordinateEquiv (Coupled.matter point))
    actionSelectedCoupled_matterCoordinates_contDiff
    0 canonicalLorentzianTimeDirection,
    coupled_matterCoordinates_temporalDerivative_zero]
  exact map_zero
    (lorentzSpinCoordinateLinear variationDirection internalPair)

private theorem dualVector_temporalDerivative_zero :
    fieldDirectionalDerivative DualVector
        0 canonicalLorentzianTimeDirection = 0 := by
  exact coupled_conjugateMatterCoordinates_temporalDerivative_zero

private theorem matterPairing_lorentzSpin_dual
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (coordinates : MatterCoordinateCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterCoordinateRealPairingBilinear
        (lorentzSpinCoordinateLinear variationDirection internalPair
          coordinates)
        (matterDualCoordinates dual) =
      (dual (lorentzSpinActionVector variationDirection internalPair
        (matterCoordinateEquiv.symm coordinates))).re := by
  rw [matterCoordinateRealPairingBilinear_matterDualCoordinates]
  have vectorFidelity :
      matterCoordinateEquiv.symm
          (lorentzSpinCoordinateLinear variationDirection internalPair
            coordinates) =
        lorentzSpinActionVector variationDirection internalPair
          (matterCoordinateEquiv.symm coordinates) := by
    simp
  rw [← vectorFidelity, matterDual_coordinate_expansion]
  simp only [Complex.re_sum]

private theorem frozenLorentzMatterCoefficient_normalForm
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient Source 0 point
        (withCoframe (toContinuumPointField Coupled point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point =>
        (Coupled.conjugateMatter point
          (lorentzSpinActionVector variationDirection internalPair
            (Coupled.matter point))).re := by
  funext point
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField, Matrix.det_one,
    abs_one, one_mul, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp only [inverseCoframeDiracGamma_identity]
  simp [lorentzSpinActionVector, Fin.sum_univ_four]

private theorem frozenLorentzMatterCoefficient_coordinateExpansion
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient Source 0 point
        (withCoframe (toContinuumPointField Coupled point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point => matterCoordinateRealPairingBilinear
        (SpinVector variationDirection internalPair point)
        (DualVector point) := by
  rw [frozenLorentzMatterCoefficient_normalForm]
  funext point
  unfold SpinVector DualVector holonomicConjugateMatterCoordinates
  rw [matterPairing_lorentzSpin_dual]
  simp

private theorem frozenLorentzMatterCoefficient_contDiff
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞ (fun point =>
      formNativeLorentzMatterFirstCoefficient Source 0 point
        (withCoframe (toContinuumPointField Coupled point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) := by
  rw [frozenLorentzMatterCoefficient_coordinateExpansion]
  exact
    (matterCoordinateRealPairingBilinear.toContinuousBilinearMap.contDiff.comp
      (spinVector_contDiff variationDirection internalPair)).clm_apply
      dualVector_contDiff

private theorem frozenLorentzMatterCoefficient_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          formNativeLorentzMatterFirstCoefficient Source 0 point
            (withCoframe (toContinuumPointField Coupled point) 1)
            (loweredLorentzBivectorOneFormCoordinate
              variationDirection internalPair))
        0 canonicalLorentzianTimeDirection = 0 := by
  rw [frozenLorentzMatterCoefficient_coordinateExpansion]
  have derivative := fieldDirectionalDerivative_continuousBilinear
    matterCoordinateRealPairingBilinear.toContinuousBilinearMap
    (SpinVector variationDirection internalPair) DualVector
    (spinVector_contDiff variationDirection internalPair) dualVector_contDiff
    0 canonicalLorentzianTimeDirection
  change
    fieldDirectionalDerivative
        (fun point => matterCoordinateRealPairingBilinear
          (SpinVector variationDirection internalPair point)
          (DualVector point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateRealPairingBilinear
          (fieldDirectionalDerivative
            (SpinVector variationDirection internalPair)
            0 canonicalLorentzianTimeDirection)
          (DualVector 0) +
        matterCoordinateRealPairingBilinear
          (SpinVector variationDirection internalPair 0)
          (fieldDirectionalDerivative DualVector
            0 canonicalLorentzianTimeDirection) at derivative
  rw [spinVector_temporalDerivative_zero,
    dualVector_temporalDerivative_zero] at derivative
  simpa using derivative

private def FrozenSpinResponse (point : BasePoint) :
    PhysicalBivectorThreeForm :=
  diracDualFormNativeActionSpinResponsePointCoframe
    Source Coupled (point, 1)

private theorem coupled_spinResponse_eq_frozen :
    diracDualFormNativeActionSpinResponseAt Source Coupled =
      FrozenSpinResponse := by
  funext point
  rw [diracDualFormNativeActionSpinResponseAt_eq_pointCoframe,
    congrFun fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one point]
  rfl

private theorem frozenSpinResponse_coordinate
    (point : BasePoint) (internalPair : Fin 6) (triple : Fin 4) :
    FrozenSpinResponse point internalPair triple =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient Source 0 point
          (withCoframe (toContinuumPointField Coupled point) 1)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) := by
  unfold FrozenSpinResponse
    diracDualFormNativeActionSpinResponsePointCoframe
    formNativePhysicalSpinCurrentThreeForm
  change
    -formNativeMatterSpinThreeForm Source 0 point
        (withCoframe (toContinuumPointField Coupled point) 1)
        internalPair triple = _
  conv_lhs =>
    rw [show triple = missingTripleOfOneForm
        (missingTripleOfOneForm triple) by
      exact (missingTripleOfOneForm_involutive triple).symm]
  rw [formNativeMatterSpinThreeForm_coordinate]

private theorem frozenSpinResponse_contDiff :
    ContDiff ℝ ∞ FrozenSpinResponse := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro triple
  rw [show
    (fun point => FrozenSpinResponse point internalPair triple) =
      fun point =>
        (-oneWedgeThreeSign (missingTripleOfOneForm triple)) *
          formNativeLorentzMatterFirstCoefficient Source 0 point
            (withCoframe (toContinuumPointField Coupled point) 1)
            (loweredLorentzBivectorOneFormCoordinate
              (missingTripleOfOneForm triple) internalPair) by
    funext point
    rw [frozenSpinResponse_coordinate]
    ring]
  exact contDiff_const.mul
    (frozenLorentzMatterCoefficient_contDiff
      (missingTripleOfOneForm triple) internalPair)

private theorem fieldDirectionalDerivative_const_mul_real_at_origin
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (scalar : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => scalar * field point)
        0 direction =
      scalar * fieldDirectionalDerivative field 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul fieldDifferentiable scalar]
  rfl

private theorem fieldDirectionalDerivative_finset_sum_real_at_origin
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldDifferentiable : ∀ index, DifferentiableAt ℝ (field index) 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      (fieldDifferentiable index).hasFDerivAt
  have sumDerivativePointwise :
      HasFDerivAt
        (fun point => ∑ index, field index point)
        (∑ index, fderiv ℝ (field index) 0) 0 := by
    convert sumDerivative using 1
    funext point
    simp
  unfold fieldDirectionalDerivative
  rw [sumDerivativePointwise.fderiv]
  simp

private theorem frozenSpinResponse_coordinate_temporalDerivative_zero
    (internalPair : Fin 6) (triple : Fin 4) :
    fieldDirectionalDerivative
        (fun point => FrozenSpinResponse point internalPair triple)
        0 canonicalLorentzianTimeDirection = 0 := by
  let direction := missingTripleOfOneForm triple
  let coefficient : BasePoint → ℝ := fun point =>
    formNativeLorentzMatterFirstCoefficient Source 0 point
      (withCoframe (toContinuumPointField Coupled point) 1)
      (loweredLorentzBivectorOneFormCoordinate direction internalPair)
  rw [show
    (fun point => FrozenSpinResponse point internalPair triple) =
      fun point => (-oneWedgeThreeSign direction) * coefficient point by
    funext point
    rw [frozenSpinResponse_coordinate]
    dsimp only [direction, coefficient]
    ring]
  rw [fieldDirectionalDerivative_const_mul_real_at_origin coefficient
    ((frozenLorentzMatterCoefficient_contDiff direction internalPair
      ).differentiable (by simp)).differentiableAt
    (-oneWedgeThreeSign direction) canonicalLorentzianTimeDirection,
    frozenLorentzMatterCoefficient_temporalDerivative_zero]
  simp

private theorem frozenSpinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative FrozenSpinResponse 0
        canonicalLorentzianTimeDirection = 0 := by
  funext internalPair triple
  rw [fieldDirectionalDerivative_pi_apply FrozenSpinResponse
    frozenSpinResponse_contDiff 0 canonicalLorentzianTimeDirection
    internalPair]
  rw [fieldDirectionalDerivative_pi_apply
    (fun point => FrozenSpinResponse point internalPair)
    (contDiff_pi.mp frozenSpinResponse_contDiff internalPair)
    0 canonicalLorentzianTimeDirection triple]
  exact frozenSpinResponse_coordinate_temporalDerivative_zero
    internalPair triple

private theorem coupled_spinResponse_contDiff :
    ContDiff ℝ ∞
      (diracDualFormNativeActionSpinResponseAt Source Coupled) := by
  rw [coupled_spinResponse_eq_frozen]
  exact frozenSpinResponse_contDiff

private theorem coupled_spinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt Source Coupled)
        0 canonicalLorentzianTimeDirection = 0 := by
  rw [coupled_spinResponse_eq_frozen]
  exact frozenSpinResponse_temporalDerivative_zero

/-- The fixed action-selected coupled occurrence has zero source-generated
spin-response temporal first germ. -/
theorem fixedP506L0ActionSelectedCoupled_spinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt
          positiveSmoothUnifiedSource
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
        0 canonicalLorentzianTimeDirection = 0 := by
  simpa [Source, Coupled] using coupled_spinResponse_temporalDerivative_zero

private def CoupledCoframeSpinResponseCarrier (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (Coupled.coframe point,
    diracDualFormNativeActionSpinResponseAt Source Coupled point)

private theorem coupledCoframeSpinResponseCarrier_differentiableAt :
    DifferentiableAt ℝ CoupledCoframeSpinResponseCarrier 0 := by
  apply DifferentiableAt.prodMk
  · rw [fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]
    exact differentiableAt_const 1
  · exact
      (coupled_spinResponse_contDiff.differentiable (by simp)).differentiableAt

private theorem
    coupledCoframeSpinResponseCarrier_temporalDerivative_zero :
    fieldDirectionalDerivative CoupledCoframeSpinResponseCarrier 0
        canonicalLorentzianTimeDirection = 0 := by
  have productDerivative :=
    (by
      rw [fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]
      exact differentiableAt_const (1 : LorentzianCoframe) :
        DifferentiableAt ℝ Coupled.coframe 0).fderiv_prodMk
      (coupled_spinResponse_contDiff.differentiable (by simp)).differentiableAt
  unfold fieldDirectionalDerivative CoupledCoframeSpinResponseCarrier
  rw [productDerivative]
  change
    ((fderiv ℝ Coupled.coframe 0)
        (coordinateDirection canonicalLorentzianTimeDirection),
      fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt Source Coupled)
        0 canonicalLorentzianTimeDirection) = 0
  rw [coupled_spinResponse_temporalDerivative_zero,
    fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]
  simp

private theorem coupled_cartanContorsion_component_differentiableAt
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        diracDualFormNativeActionCartanContorsionAt Source Coupled point
          formDirection internalPair) 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt Source Coupled 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : CoupledCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold CoupledCoframeSpinResponseCarrier response
    rw [congrFun fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one 0]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (CoupledCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact cartanContorsionCoframeResponseComponent_differentiableAt
      (1 : LorentzianCoframe) response (by simp)
      formDirection internalPair
  change DifferentiableAt ℝ
    (outer ∘ CoupledCoframeSpinResponseCarrier) 0
  exact outerDifferentiable.comp 0
    coupledCoframeSpinResponseCarrier_differentiableAt

private theorem coupled_cartanContorsion_component_temporalDerivative_zero_internal
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt Source Coupled point
            formDirection internalPair)
        0 canonicalLorentzianTimeDirection = 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt Source Coupled 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : CoupledCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold CoupledCoframeSpinResponseCarrier response
    rw [congrFun fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one 0]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (CoupledCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact cartanContorsionCoframeResponseComponent_differentiableAt
      (1 : LorentzianCoframe) response (by simp)
      formDirection internalPair
  have composition := outerDifferentiable.hasFDerivAt.comp 0
    coupledCoframeSpinResponseCarrier_differentiableAt.hasFDerivAt
  change fieldDirectionalDerivative
      (outer ∘ CoupledCoframeSpinResponseCarrier)
      0 canonicalLorentzianTimeDirection = 0
  unfold fieldDirectionalDerivative
  rw [composition.fderiv]
  change
    (fderiv ℝ outer (CoupledCoframeSpinResponseCarrier 0))
        (fieldDirectionalDerivative CoupledCoframeSpinResponseCarrier 0
          canonicalLorentzianTimeDirection) = 0
  rw [coupledCoframeSpinResponseCarrier_temporalDerivative_zero]
  simp

/-- The source-generated KIN-3/KIN-2 contorsion of the fixed action-selected
coupled current has zero temporal first germ at the origin. -/
theorem
    fixedP506L0ActionSelectedCoupled_cartanContorsion_component_temporalDerivative_zero
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            (completeJointActionSelectedCoupledTemporalActual
              positiveSmoothUnifiedSource
              fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
            point formDirection internalPair)
        0 canonicalLorentzianTimeDirection = 0 := by
  simpa [Source, Coupled] using
    coupled_cartanContorsion_component_temporalDerivative_zero_internal
      formDirection internalPair

private theorem coupled_cartanSkew_component_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt Source Coupled point)
          formDirection internalOut internalIn) 0 := by
  unfold lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  apply DifferentiableAt.mul (differentiableAt_const _)
  rw [show
    (fun point =>
      ∑ pair : Fin 6,
        diracDualFormNativeActionCartanContorsionAt Source Coupled point
            formDirection pair *
          orientedLorentzBivectorBasisCoefficient pair internalOut
            internalIn) =
      ∑ pair : Fin 6, fun point =>
        diracDualFormNativeActionCartanContorsionAt Source Coupled point
            formDirection pair *
          orientedLorentzBivectorBasisCoefficient pair internalOut
            internalIn by
    funext point
    simp]
  exact DifferentiableAt.sum fun internalPair _ =>
    (coupled_cartanContorsion_component_differentiableAt
      formDirection internalPair).mul (differentiableAt_const _)

private theorem coupled_cartanSkew_component_temporalDerivative_zero
    (formDirection internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt Source Coupled point)
            formDirection internalOut internalIn)
        0 canonicalLorentzianTimeDirection = 0 := by
  let summand : Fin 6 → BasePoint → ℝ := fun internalPair point =>
    diracDualFormNativeActionCartanContorsionAt Source Coupled point
        formDirection internalPair *
      orientedLorentzBivectorBasisCoefficient internalPair internalOut
        internalIn
  have summandDifferentiable (internalPair : Fin 6) :
      DifferentiableAt ℝ (summand internalPair) 0 :=
    (coupled_cartanContorsion_component_differentiableAt
      formDirection internalPair).mul (differentiableAt_const _)
  rw [show
    (fun point =>
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeActionCartanContorsionAt Source Coupled point)
        formDirection internalOut internalIn) =
      fun point =>
        minkowskiInternalSign internalOut *
          ∑ internalPair : Fin 6, summand internalPair point by
    funext point
    rfl]
  rw [fieldDirectionalDerivative_const_mul_real_at_origin _
    (by
      rw [show
        (fun point => ∑ internalPair : Fin 6, summand internalPair point) =
          ∑ internalPair : Fin 6, summand internalPair by
        funext point
        simp]
      exact DifferentiableAt.sum fun internalPair _ =>
        summandDifferentiable internalPair)
    (minkowskiInternalSign internalOut)
    canonicalLorentzianTimeDirection,
    fieldDirectionalDerivative_finset_sum_real_at_origin summand
      summandDifferentiable canonicalLorentzianTimeDirection]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro internalPair _
  rw [show summand internalPair = fun point =>
      orientedLorentzBivectorBasisCoefficient internalPair internalOut
          internalIn *
        diracDualFormNativeActionCartanContorsionAt Source Coupled point
          formDirection internalPair by
    funext point
    dsimp only [summand]
    ring]
  rw [fieldDirectionalDerivative_const_mul_real_at_origin _
    (coupled_cartanContorsion_component_differentiableAt
      formDirection internalPair)
    (orientedLorentzBivectorBasisCoefficient internalPair internalOut
      internalIn)
    canonicalLorentzianTimeDirection,
    coupled_cartanContorsion_component_temporalDerivative_zero_internal]
  simp

private theorem coupled_leviCivita_component_eq_zero
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    (holonomicCoframeFirstJetAt Coupled.coframe point).lorentzSpinConnection
        formDirection internalOut internalIn = 0 :=
  currentIdentityCoframe_leviCivita_component_eq_zero Coupled
    fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one point
      formDirection internalOut internalIn

private theorem coupled_leviCivita_component_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        (holonomicCoframeFirstJetAt Coupled.coframe point
          ).lorentzSpinConnection formDirection internalOut internalIn) 0 := by
  rw [show
    (fun point =>
      (holonomicCoframeFirstJetAt Coupled.coframe point
        ).lorentzSpinConnection formDirection internalOut internalIn) =
      fun _ => (0 : ℝ) by
    funext point
    exact coupled_leviCivita_component_eq_zero point
      formDirection internalOut internalIn]
  fun_prop

private theorem coupled_leviCivita_component_temporalDerivative_zero
    (formDirection internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
      (fun point =>
        (holonomicCoframeFirstJetAt Coupled.coframe point
          ).lorentzSpinConnection formDirection internalOut internalIn)
      0 canonicalLorentzianTimeDirection = 0 := by
  rw [show
    (fun point =>
      (holonomicCoframeFirstJetAt Coupled.coframe point
        ).lorentzSpinConnection formDirection internalOut internalIn) =
      fun _ => (0 : ℝ) by
    funext point
    exact coupled_leviCivita_component_eq_zero point
      formDirection internalOut internalIn]
  simp [fieldDirectionalDerivative]

private theorem fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

/-! The coupled temporal producer preserves the complete pointwise Cartan
connection to first order in the canonical time direction.  The two trace
coordinates below are projections of this whole-connection fact. -/
theorem
    fixedP506L0ActionSelectedCoupled_cartanConnection_component_temporalDerivative_zero
    (formDirection internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt Source Coupled point
            formDirection internalOut internalIn)
        0 canonicalLorentzianTimeDirection = 0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt Coupled.coframe point
            ).lorentzSpinConnection formDirection internalOut internalIn +
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt Source Coupled point)
            formDirection internalOut internalIn)
        0 canonicalLorentzianTimeDirection = 0
  rw [fieldDirectionalDerivative_add_real_at_origin _ _
    (coupled_leviCivita_component_differentiableAt
      formDirection internalOut internalIn)
    (coupled_cartanSkew_component_differentiableAt
      formDirection internalOut internalIn)
    canonicalLorentzianTimeDirection,
    coupled_leviCivita_component_temporalDerivative_zero,
    coupled_cartanSkew_component_temporalDerivative_zero]
  norm_num

private theorem successor_connection_eq_cartan :
    Successor.gravityConnection = Cartan.gravityConnection :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
    Source Coupled

/-- The first successor connection component entering the faithful gravity
tail Lorentz trace has zero temporal first jet at the fixed origin. -/
theorem
    fixedP506L0ActionSelectedJointSuccessor_connection212_temporalDerivative_zero :
    gravityConnectionDerivative Successor 0
        canonicalLorentzianTimeDirection 2 1 2 = 0 := by
  unfold gravityConnectionDerivative
  rw [successor_connection_eq_cartan,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact
    fixedP506L0ActionSelectedCoupled_cartanConnection_component_temporalDerivative_zero
      2 1 2

/-- The second successor connection component entering the same trace also
has zero temporal first jet. -/
theorem
    fixedP506L0ActionSelectedJointSuccessor_connection331_temporalDerivative_zero :
    gravityConnectionDerivative Successor 0
        canonicalLorentzianTimeDirection 3 3 1 = 0 := by
  unfold gravityConnectionDerivative
  rw [successor_connection_eq_cartan,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact
    fixedP506L0ActionSelectedCoupled_cartanConnection_component_temporalDerivative_zero
      3 3 1

/-- The complete predecessor trace subtracted by the gravity-tail Lorentz
support therefore vanishes on the same action-selected occurrence. -/
theorem fixedP506L0ActionSelectedJointSuccessor_connectionTemporalTrace_zero :
    gravityConnectionDerivative Successor 0
          canonicalLorentzianTimeDirection 2 1 2 -
        gravityConnectionDerivative Successor 0
          canonicalLorentzianTimeDirection 3 3 1 = 0 := by
  rw [
    fixedP506L0ActionSelectedJointSuccessor_connection212_temporalDerivative_zero,
    fixedP506L0ActionSelectedJointSuccessor_connection331_temporalDerivative_zero]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedJointSuccessorLorentzTemporalTrace
