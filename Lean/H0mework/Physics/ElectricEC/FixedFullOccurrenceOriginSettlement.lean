import H0mework.Physics.ElectricJoint.ElectricECFullOccurrenceContactOperator
import H0mework.Physics.ElectricEC.FixedMatterScalarDeltas
import H0mework.Physics.ElectricEC.FixedP286AllPointSettlement

/-!
# Fixed P506/L0 full-occurrence origin settlement

For every occurrence in the generated nondegenerate component, the
source/current-only full-occurrence operator first recenters the authoritative
`U5` current and then reruns the same five action legs.  This module reads the
result only at that contact's local origin.

The rerun Cartan leg closes the Lorentz equation on its own live fields.  The
Einstein--Cartan suffix preserves that local-origin read, so the old `U5`
changed-read is not transported into the new contact.  The two algebraic
gravity channels and the live P286 auxiliary channel close directly.  The
complete residual therefore reduces exactly to the native P286 connection
read, three native-plus-changed-read telescopes, and the coframe read.  On the
whole generated zero-time slice the coframe read closes as well.

Every support below is a readout of the action-generated contact.  No residual,
support coordinate, target field, branch, or zero-fiber receipt enters a
constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceOriginSettlement

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyMatterScalarReadTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECP286AllPointSettlement
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Recentered
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration FixedCurrent contact

private abbrev Temporal
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (Recentered contact)

private abbrev Algebraic
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source (Recentered contact)

private abbrev LiveP286
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current Source (Recentered contact)

private abbrev Cartan
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    Source (Recentered contact)

private abbrev Final
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact contact

/-! ## Primitive seams of the action-owned suffix -/

private theorem final_coframe_eq_live
    (contact : BasePoint) :
    (Final contact).coframe = (LiveP286 contact).coframe := by
  calc
    (Final contact).coframe = (Cartan contact).coframe :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe
        Source (Cartan contact)
    _ = (LiveP286 contact).coframe :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        Source (LiveP286 contact)

private theorem final_gaugeConnection_eq_live
    (contact : BasePoint) :
    (Final contact).gaugeConnection = (LiveP286 contact).gaugeConnection := by
  calc
    (Final contact).gaugeConnection = (Cartan contact).gaugeConnection :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection
        Source (Cartan contact)
    _ = (LiveP286 contact).gaugeConnection :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        Source (LiveP286 contact)

private theorem final_gaugeAuxiliary_eq_live
    (contact : BasePoint) :
    (Final contact).gaugeAuxiliary = (LiveP286 contact).gaugeAuxiliary := by
  calc
    (Final contact).gaugeAuxiliary = (Cartan contact).gaugeAuxiliary :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary
        Source (Cartan contact)
    _ = (LiveP286 contact).gaugeAuxiliary :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
        Source (LiveP286 contact)

private theorem final_scalar_eq_live
    (contact : BasePoint) :
    (Final contact).scalar = (LiveP286 contact).scalar := by
  calc
    (Final contact).scalar = (Cartan contact).scalar :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar
        Source (Cartan contact)
    _ = (LiveP286 contact).scalar :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        Source (LiveP286 contact)

private theorem final_matter_eq_live
    (contact : BasePoint) :
    (Final contact).matter = (LiveP286 contact).matter := by
  calc
    (Final contact).matter = (Cartan contact).matter :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter
        Source (Cartan contact)
    _ = (LiveP286 contact).matter :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
        Source (LiveP286 contact)

private theorem final_conjugateMatter_eq_live
    (contact : BasePoint) :
    (Final contact).conjugateMatter =
        (LiveP286 contact).conjugateMatter := by
  calc
    (Final contact).conjugateMatter = (Cartan contact).conjugateMatter :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter
        Source (Cartan contact)
    _ = (LiveP286 contact).conjugateMatter :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
        Source (LiveP286 contact)

/-! ## Contact-native Cartan settlement -/

private theorem fixedCurrent_coframe_contDiff :
    ContDiff ℝ ∞ FixedCurrent.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
      internal coordinate

private theorem recentered_coframe_contDiff
    (contact : BasePoint) :
    ContDiff ℝ ∞ (Recentered contact).coframe := by
  have translationSmooth :
      ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation contact) := by
    unfold canonicalSpacetimeContactTranslation
    fun_prop
  change ContDiff ℝ ∞
    (fun point => FixedCurrent.coframe
      (canonicalSpacetimeContactTranslation contact point))
  exact fixedCurrent_coframe_contDiff.comp translationSmooth

private theorem liveP286_coframe_contDiff
    (contact : BasePoint) :
    ContDiff ℝ ∞ (LiveP286 contact).coframe := by
  rw [←
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
      Source (LiveP286 contact)]
  change ContDiff ℝ ∞ (Cartan contact).coframe
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe]
  exact recentered_coframe_contDiff contact

private theorem fixedCurrent_coframe_nondegenerate_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        (FixedCurrent.coframe
          (canonicalCauchySlicePoint time space)) ≠
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
      space inDomain

private theorem liveP286_coframe_origin_nondegenerate_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        ((LiveP286 (canonicalCauchySlicePoint time space)).coframe 0) ≠
      0 := by
  rw [←
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
      Source
      (LiveP286 (canonicalCauchySlicePoint time space))]
  change Matrix.det
      ((Cartan (canonicalCauchySlicePoint time space)).coframe 0) ≠ 0
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]
  exact fixedCurrent_coframe_nondegenerate_onDomain time space inDomain

private theorem cartan_lorentz_origin_zero_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    holonomicFormNativeLorentzEulerThreeForm Source 0
        (Cartan (canonicalCauchySlicePoint time space)) 0 =
      0 := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      Source
      (LiveP286 (canonicalCauchySlicePoint time space))
      (liveP286_coframe_contDiff
        (canonicalCauchySlicePoint time space))
      0
      (liveP286_coframe_origin_nondegenerate_onDomain
        time space inDomain)

/-! ## Einstein--Cartan origin preservation of the Lorentz read -/

private theorem ecFullCauchy_matterSpin_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    formNativeMatterSpinThreeForm source 0 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) 0) =
      formNativeMatterSpinThreeForm source 0 0
        (toContinuumPointField current 0) := by
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      source
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current)
      current 0
      (congrFun
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe
          source current) 0)
      (congrFun
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter
          source current) 0)
      (congrFun
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter
          source current) 0)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
  exact neg_injective physicalSpinEquality

private theorem ecFullCauchy_lorentz_origin_eq_cartan
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current)) 0 =
      holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) 0 := by
  unfold holonomicFormNativeLorentzEulerThreeForm
  have auxiliaryDerivativeEq :
      holonomicGravityAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current)) 0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) 0 := by
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
        source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)]
    rfl
  rw [auxiliaryDerivativeEq,
    ecFullCauchy_matterSpin_origin_eq_current source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current)]

/-- The full-occurrence rerun closes the complete Lorentz Euler reader at its
own local origin on every occurrence in the generated nondegenerate domain.
The theorem is computed from that contact's live Cartan fields; it does not
transport the old `U5` Lorentz residual. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_lorentz_origin_zero
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final (canonicalCauchySlicePoint time space)) 0).lorentzConnection =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm Source 0
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift Source
          (Cartan (canonicalCauchySlicePoint time space))) 0 =
      0
  calc
    holonomicFormNativeLorentzEulerThreeForm Source 0
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift Source
          (Cartan (canonicalCauchySlicePoint time space))) 0 =
      holonomicFormNativeLorentzEulerThreeForm Source 0
        (Cartan (canonicalCauchySlicePoint time space)) 0 :=
          ecFullCauchy_lorentz_origin_eq_cartan Source
            (LiveP286 (canonicalCauchySlicePoint time space))
    _ = 0 := cartan_lorentz_origin_zero_onDomain time space inDomain

/-! ## Algebraic gravity settlement -/

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_gravityMultiplier_origin_zero
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField (Final contact) 0) =
      0
  exact
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        Source (Cartan contact) 0)

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_gravityAuxiliary_origin_zero
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).gravityAuxiliary =
      0 := by
  change holonomicFormNativeGravityAuxiliaryEulerResidual (Final contact) 0 = 0
  exact congrFun
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
      Source (Cartan contact)) 0

/-! ## Native P286 critical pair and algebraic settlement -/

private theorem final_p286Auxiliary_origin_eq_live
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).p286GaugeAuxiliary =
      (diracDualFormNativePointwiseJointResidual Source
        (LiveP286 contact) 0).p286GaugeAuxiliary := by
  have curvatureEq :
      holonomicGaugeCurvature (Final contact) 0 =
        holonomicGaugeCurvature (LiveP286 contact) 0 :=
    holonomicGaugeCurvature_eq_of_connection_eq
      (Final contact) (LiveP286 contact)
      (final_gaugeConnection_eq_live contact) 0
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (Final contact) 0) =
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (LiveP286 contact) 0)
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
  simp only [toContinuumPointField]
  rw [curvatureEq, final_coframe_eq_live contact,
    final_gaugeAuxiliary_eq_live contact]

private theorem final_p286Connection_origin_eq_live
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual Source
        (LiveP286 contact) 0).p286GaugeConnection := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (Final contact) 0 =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (LiveP286 contact) 0
  exact congrFun
    (holonomicFormNativeP286GaugeEulerThreeForm_eq_of_primitiveFields
      Source (Final contact) (LiveP286 contact)
      (final_coframe_eq_live contact)
      (final_gaugeConnection_eq_live contact)
      (final_gaugeAuxiliary_eq_live contact)
      (final_scalar_eq_live contact)
      (final_matter_eq_live contact)
      (final_conjugateMatter_eq_live contact)) 0

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem liveP286_gaugeAuxiliary_origin_eq_algebraic
    (contact : BasePoint) :
    (LiveP286 contact).gaugeAuxiliary 0 =
      (Algebraic contact).gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have cartanCoordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate (Cartan contact) 0 pair =
        holonomicP286GaugeAuxiliaryCoordinate (Algebraic contact) 0 pair := by
    have zeroSliceEquality := congrFun
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
        Source (Recentered contact) (0 : StageNineSpatialPoint)) pair
    simpa only [canonicalCauchySlicePoint_zero_zero] using zeroSliceEquality
  have cartanAuxiliaryEquality :
      (Cartan contact).gaugeAuxiliary 0 pair =
        (LiveP286 contact).gaugeAuxiliary 0 pair :=
    congrFun (congrFun
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
        Source (LiveP286 contact)) 0) pair
  calc
    p286CoordinateEquiv ((LiveP286 contact).gaugeAuxiliary 0 pair) =
        p286CoordinateEquiv ((Cartan contact).gaugeAuxiliary 0 pair) :=
      congrArg p286CoordinateEquiv cartanAuxiliaryEquality.symm
    _ = p286CoordinateEquiv
          ((Algebraic contact).gaugeAuxiliary 0 pair) :=
      cartanCoordinateEquality

private theorem liveP286_p286Auxiliary_origin_zero_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    (diracDualFormNativePointwiseJointResidual Source
      (LiveP286 (canonicalCauchySlicePoint time space)) 0
      ).p286GaugeAuxiliary =
      0 := by
  let contact := canonicalCauchySlicePoint time space
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (LiveP286 contact) 0) =
      0
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (LiveP286 contact) 0)).2
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (LiveP286 contact) 0)
      (liveP286_coframe_origin_nondegenerate_onDomain
        time space inDomain)).2
  change
    (LiveP286 contact).gaugeAuxiliary 0 =
      diracDualFormNativeConstitutiveAuxiliaryField Source
        (LiveP286 contact) 0
  calc
    (LiveP286 contact).gaugeAuxiliary 0 =
        (Algebraic contact).gaugeAuxiliary 0 :=
      liveP286_gaugeAuxiliary_origin_eq_algebraic contact
    _ = diracDualFormNativeConstitutiveAuxiliaryField Source
          (Algebraic contact) 0 :=
      (completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
        Source (Recentered contact) 0).symm
    _ = diracDualFormNativeConstitutiveAuxiliaryField Source
          (LiveP286 contact) 0 := by
      rfl

/-- The source-owned live-electric Cauchy anchor settles the P286 algebraic
reader at every recentered contact origin in the generated nondegenerate
domain.  The EC suffix only transports this already generated value. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_p286Auxiliary_origin_zero
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final (canonicalCauchySlicePoint time space)) 0
      ).p286GaugeAuxiliary =
      0 := by
  rw [final_p286Auxiliary_origin_eq_live]
  exact liveP286_p286Auxiliary_origin_zero_onDomain time space inDomain

/-- The two coupled P286 readers are kept as one typed action-native pair.
They are read on the generated live-electric leg before the gravity-only
suffix, not reconstructed from the final support. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceNativeP286Pair
    (contact : BasePoint) :
    FormNativeP286GaugeTwoForm × P286GaugeThreeForm :=
  ((diracDualFormNativePointwiseJointResidual Source
      (LiveP286 contact) 0).p286GaugeAuxiliary,
    (diracDualFormNativePointwiseJointResidual Source
      (LiveP286 contact) 0).p286GaugeConnection)

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalP286Pair_eq_native
    (contact : BasePoint) :
    ((diracDualFormNativePointwiseJointResidual Source
        (Final contact) 0).p286GaugeAuxiliary,
      (diracDualFormNativePointwiseJointResidual Source
        (Final contact) 0).p286GaugeConnection) =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceNativeP286Pair
        contact := by
  apply Prod.ext
  · exact final_p286Auxiliary_origin_eq_live contact
  · exact final_p286Connection_origin_eq_live contact

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_nativeP286Auxiliary_origin_zero
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceNativeP286Pair
      (canonicalCauchySlicePoint time space)).1 =
      0 := by
  exact liveP286_p286Auxiliary_origin_zero_onDomain time space inDomain

/-! ## Matter/scalar telescoping support -/

/-- Native temporal scalar read plus the actual P286-algebraic changed read.
The live-electric, Cartan, and EC legs are scalar-silent. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceScalarSupport
    (contact : BasePoint) : ScalarCoordinateCarrier → ℝ :=
  let temporal :=
    (diracDualFormNativePointwiseJointResidual Source (Temporal contact) 0).scalar
  let algebraic :=
    (diracDualFormNativePointwiseJointResidual Source (Algebraic contact) 0).scalar
  temporal + (algebraic - temporal)

/-- Native temporal matter read plus the P286-algebraic and Cartan changed
reads.  The live-electric edge and the occurrence-local EC edge are silent. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceMatterSupport
    (contact : BasePoint) : MatterCoordinateCarrier → ℝ :=
  let temporal :=
    (diracDualFormNativePointwiseJointResidual Source (Temporal contact) 0).matter
  let algebraic :=
    (diracDualFormNativePointwiseJointResidual Source (Algebraic contact) 0).matter
  let live :=
    (diracDualFormNativePointwiseJointResidual Source (LiveP286 contact) 0).matter
  let cartan :=
    (diracDualFormNativePointwiseJointResidual Source (Cartan contact) 0).matter
  temporal + (algebraic - temporal) + (cartan - live)

/-- Adjoint analogue of the exact native-plus-changed-read decomposition. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceConjugateMatterSupport
    (contact : BasePoint) : MatterCoordinateCarrier → ℝ :=
  let temporal :=
    (diracDualFormNativePointwiseJointResidual Source
      (Temporal contact) 0).conjugateMatter
  let algebraic :=
    (diracDualFormNativePointwiseJointResidual Source
      (Algebraic contact) 0).conjugateMatter
  let live :=
    (diracDualFormNativePointwiseJointResidual Source
      (LiveP286 contact) 0).conjugateMatter
  let cartan :=
    (diracDualFormNativePointwiseJointResidual Source
      (Cartan contact) 0).conjugateMatter
  temporal + (algebraic - temporal) + (cartan - live)

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalScalar_eq_support
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).scalar =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceScalarSupport
        contact := by
  have cartanEqLive :
      (diracDualFormNativePointwiseJointResidual Source
        (Cartan contact) 0).scalar =
        (diracDualFormNativePointwiseJointResidual Source
          (LiveP286 contact) 0).scalar := by
    change
      (diracDualFormNativePointwiseJointResidual Source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source (LiveP286 contact)) 0).scalar = _
    exact
      StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas.sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalarResidual_eq_current
        Source (LiveP286 contact) 0
  have liveEqAlgebraic :
      (diracDualFormNativePointwiseJointResidual Source
        (LiveP286 contact) 0).scalar =
        (diracDualFormNativePointwiseJointResidual Source
          (Algebraic contact) 0).scalar := by
    change
      (diracDualFormNativePointwiseJointResidual Source
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          Source (Algebraic contact)) 0).scalar = _
    exact
      StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas.sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_scalarResidual_eq_current
        Source (Algebraic contact) 0
  change
    (diracDualFormNativePointwiseJointResidual Source
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        Source (Cartan contact)) 0).scalar = _
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalarResidual_eq_current
      Source (Cartan contact) 0]
  rw [cartanEqLive, liveEqAlgebraic]
  unfold
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceScalarSupport
  abel

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalMatter_eq_support
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).matter =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceMatterSupport
        contact := by
  have liveEqAlgebraic :
      (diracDualFormNativePointwiseJointResidual Source
        (LiveP286 contact) 0).matter =
        (diracDualFormNativePointwiseJointResidual Source
          (Algebraic contact) 0).matter := by
    change
      (diracDualFormNativePointwiseJointResidual Source
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          Source (Algebraic contact)) 0).matter = _
    exact
      StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas.sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_matterResidual_eq_current
        Source (Algebraic contact) 0
  change
    (diracDualFormNativePointwiseJointResidual Source
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        Source (Cartan contact)) 0).matter = _
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matterResidual_eq_current_of_connection_eq
      Source (Cartan contact) 0
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
        Source (Cartan contact))]
  unfold
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceMatterSupport
  rw [liveEqAlgebraic]
  abel

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalConjugateMatter_eq_support
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final contact) 0).conjugateMatter =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceConjugateMatterSupport
        contact := by
  have liveEqAlgebraic :
      (diracDualFormNativePointwiseJointResidual Source
        (LiveP286 contact) 0).conjugateMatter =
        (diracDualFormNativePointwiseJointResidual Source
          (Algebraic contact) 0).conjugateMatter := by
    change
      (diracDualFormNativePointwiseJointResidual Source
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          Source (Algebraic contact)) 0).conjugateMatter = _
    exact
      StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas.sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_conjugateMatterResidual_eq_current
        Source (Algebraic contact) 0
  change
    (diracDualFormNativePointwiseJointResidual Source
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        Source (Cartan contact)) 0).conjugateMatter = _
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatterResidual_eq_current_of_connection_eq
      Source (Cartan contact) 0
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
        Source (Cartan contact))]
  unfold
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceConjugateMatterSupport
  rw [liveEqAlgebraic]
  abel

/-! ## Whole-carrier compression -/

/-- Exactly the channels not already closed by the algebraic gravity,
P286-auxiliary, and contact-native Lorentz action legs. -/
structure FullOccurrenceRemainingOriginSupport where
  p286Connection : P286GaugeThreeForm
  scalar : ScalarCoordinateCarrier → ℝ
  matter : MatterCoordinateCarrier → ℝ
  conjugateMatter : MatterCoordinateCarrier → ℝ
  coframe : LorentzianCoframe →L[ℝ] ℝ

def fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
    (contact : BasePoint) : FullOccurrenceRemainingOriginSupport :=
  let residual :=
    diracDualFormNativePointwiseJointResidual Source (Final contact) 0
  { p286Connection :=
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceNativeP286Pair
        contact).2
    scalar :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceScalarSupport contact
    matter :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceMatterSupport contact
    conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceConjugateMatterSupport
        contact
    coframe := residual.coframe }

def FullOccurrenceRemainingOriginSupport.asJointResidual
    (support : FullOccurrenceRemainingOriginSupport) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier := 0
    gravityAuxiliary := 0
    p286GaugeAuxiliary := 0
    lorentzConnection := 0
    p286GaugeConnection := support.p286Connection
    scalar := support.scalar
    matter := support.matter
    conjugateMatter := support.conjugateMatter
    coframe := support.coframe }

/-- Exact whole-carrier normal form of the rerun contact residual.  Four
channels are settled; the remaining five coordinates are the native P286
connection reader, three exact native-plus-changed-read telescopes, and the
coframe reader. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_originResidual_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    diracDualFormNativePointwiseJointResidual Source
        (Final (canonicalCauchySlicePoint time space)) 0 =
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
        (canonicalCauchySlicePoint time space)).asJointResidual := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_gravityMultiplier_origin_zero
        (canonicalCauchySlicePoint time space)
  · exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_gravityAuxiliary_origin_zero
        (canonicalCauchySlicePoint time space)
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0
          ).p286GaugeAuxiliary =
        0
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_p286Auxiliary_origin_zero
        time space inDomain
  · exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_lorentz_origin_zero
        time space inDomain
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0
          ).p286GaugeConnection =
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceNativeP286Pair
          (canonicalCauchySlicePoint time space)).2
    exact final_p286Connection_origin_eq_live
      (canonicalCauchySlicePoint time space)
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0).scalar =
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceScalarSupport
          (canonicalCauchySlicePoint time space)
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalScalar_eq_support
        (canonicalCauchySlicePoint time space)
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0).matter =
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceMatterSupport
          (canonicalCauchySlicePoint time space)
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalMatter_eq_support
        (canonicalCauchySlicePoint time space)
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0
          ).conjugateMatter =
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceConjugateMatterSupport
          (canonicalCauchySlicePoint time space)
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrence_finalConjugateMatter_eq_support
        (canonicalCauchySlicePoint time space)
  · change
      (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0).coframe =
        (diracDualFormNativePointwiseJointResidual Source
          (Final (canonicalCauchySlicePoint time space)) 0).coframe
    rfl

/-- The generated action jet factors through the same compressed residual.
This is the all-point action-jet readout requested by the full-occurrence
kernel; no old-current residual is transported across the write. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_actionJetResidual_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    diracDualFormNativeJointResidualOfActionJet Source 0
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceActionJet
          (canonicalCauchySlicePoint time space)) =
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
        (canonicalCauchySlicePoint time space)).asJointResidual := by
  change
    diracDualFormNativeJointResidualOfActionJet Source 0
        (generatedDiracDualFormNativePointwiseActionJet Source
          (Final (canonicalCauchySlicePoint time space)) 0) =
      _
  rw [← diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_originResidual_normalForm
      time space inDomain

/-! ## Whole zero-time coframe settlement -/

private theorem fixedCurrent_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    FixedCurrent.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice space

private theorem cartan_coframe_origin_one_zeroSlice
    (space : StageNineSpatialPoint) :
    (Cartan (canonicalCauchySlicePoint 0 space)).coframe 0 = 1 := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]
  exact fixedCurrent_coframe_zeroSlice space

/-- The full Einstein--Cartan leg closes the coframe equation at every
recentered contact on the generated zero-time slice. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_coframe_origin_zero_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Final (canonicalCauchySlicePoint 0 space)) 0).coframe =
      0 := by
  change
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift Source
            (Cartan (canonicalCauchySlicePoint 0 space))) 0) =
      0
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_fullCoframeEuler_zero
      Source (Cartan (canonicalCauchySlicePoint 0 space))
      (cartan_coframe_origin_one_zeroSlice space)

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_remainingCoframe_zero_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceRemainingOriginSupport
      (canonicalCauchySlicePoint 0 space)).coframe =
      0 := by
  change
    (diracDualFormNativePointwiseJointResidual Source
      (Final (canonicalCauchySlicePoint 0 space)) 0).coframe = 0
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_coframe_origin_zero_zeroSlice
      space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceOriginSettlement
