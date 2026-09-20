import H0mework.Physics.ConstitutiveAction.SpatialSectionGaugeClosure
import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointFirstJet
import H0mework.Physics.FixedJoint.FixedJointResidual

/-!
# Residual of the repaired constitutive spatial section

The repaired source/current-only operator and its single four-dimensional
spatial section already exist before this file.  This module substitutes that
actual into the authoritative nine-channel residual and computes the two
algebraic channels, the gravity-curvature seam, and the Lorentz channel.

Every result here is a diagnostic readout.  No residual coordinate, sign,
support branch, or zero-fiber witness is accepted by an action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev SectionActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem canonicalSpatialContactTranslation_zero
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  simpa only [canonicalCauchySlicePoint_zero_zero] using
    canonicalSpatialContactTranslation_timeAxis space 0

/-! ## Algebraic channels -/

/-- Contactwise simplicity assembles to one global simplicity law for the
already-generated repaired section. -/
theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        source current) := by
  intro point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe_slice]
  exact
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_simplicity
      source
      (spatiallyRecenterHolonomicConfiguration current
        (canonicalSpatialProjection point))
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_simplicity :
    FormNativeGravitySimplicityEquation SectionActual :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_simplicity
    positiveSmoothUnifiedSource InputActual

/-- Authoritative nine-channel residual section, defined strictly downstream
of the repaired producer. -/
def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    SectionActual

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      point).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField SectionActual point) =
      0
  apply
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField SectionActual point)).2
  exact
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_simplicity
      point

/-- The repaired local EC lift always installs `II⁺(e)` as its gravity
auxiliary; the repaired matter write does not alter the coframe. -/
@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) := by
  rfl

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) := by
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityAuxiliary]
  simp [spatiallyRecenterHolonomicConfiguration]

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation current) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravityAuxiliary =
      current.gravityAuxiliary := by
  funext point
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary
      source current point]
  exact (simplicity point).symm

/-! ## P286 auxiliary channel -/

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        source current).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (current.coframe point)
        (holonomicGaugeCurvature current point) := by
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeAuxiliary]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [holonomicGaugeCurvature_spatiallyRecenter current smooth,
    canonicalSpatialContactTranslation_timeAxis]
  simp [spatiallyRecenterHolonomicConfiguration]

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_curvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          source current) point =
      holonomicGaugeCurvature current point := by
  exact
    holonomicGaugeCurvature_eq_of_connection_eq_current
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        source current)
      current
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        source current)
      point

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          source current) point) := by
  let output :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current
  have outputCoframe :
      output.coframe = current.coframe :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
      source current
  have outputCurvature :
      holonomicGaugeCurvature output point =
        holonomicGaugeCurvature current point :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_curvature
      source current point
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField output point)
      (by
        change Matrix.det (output.coframe point) ≠ 0
        rw [outputCoframe]
        exact nondegenerate)).2
  change
    output.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (output.coframe point)
        (holonomicGaugeCurvature output point)
  rw [outputCoframe, outputCurvature]
  exact
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      source current smooth point

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary =
      0 := by
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField SectionActual
        (canonicalCauchySlicePoint 0 space))).2
  apply
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliaryEquation
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth
  · rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
    norm_num

/-! ## Gravity curvature and Lorentz channels -/

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravityConnection (canonicalCauchySlicePoint 0 space) =
      current.gravityConnection (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero]
  exact congrArg current.gravityConnection
    (canonicalSpatialContactTranslation_zero space)

/-- The repaired primal and adjoint writes are linear-time writes, hence
preserve both matter values at their contact origin. -/
@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).matter 0 =
      current.matter 0 := by
  rw [diracDualFormNativeRepairedConstitutiveJointActionResponseOperator,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]
  unfold diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      source current).conjugateMatter 0 =
      current.conjugateMatter 0 := by
  rw [diracDualFormNativeRepairedConstitutiveJointActionResponseOperator,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]
  unfold diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  rfl

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).matter (canonicalCauchySlicePoint 0 space) =
      current.matter (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter_zero]
  exact congrArg current.matter
    (canonicalSpatialContactTranslation_zero space)

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      current.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice,
    canonicalCauchySlicePoint_zero_zero,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter_zero]
  exact congrArg current.conjugateMatter
    (canonicalSpatialContactTranslation_zero space)

/-- Lorentz residual preservation follows from literal whole-field
auxiliary equality and same-slice primitive values.  It transports no
residual receipt. -/
theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_lorentzResidual_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation current)
    (space : StageNineSpatialPoint) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicFormNativeLorentzEulerThreeForm source 0 current
        (canonicalCauchySlicePoint 0 space) := by
  let output :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current
  let point := canonicalCauchySlicePoint 0 space
  have auxiliaryEquality :
      output.gravityAuxiliary = current.gravityAuxiliary :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_eq_current
      source current simplicity
  have connectionEquality :
      output.gravityConnection point = current.gravityConnection point :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_zeroSlice
      source current space
  have covariantDerivativeEquality :
      holonomicGravityAuxiliaryExteriorCovariantDerivative output point =
        holonomicGravityAuxiliaryExteriorCovariantDerivative current point := by
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [auxiliaryEquality, connectionEquality]
  have coframeEquality :
      output.coframe point = current.coframe point :=
    congrFun
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        source current)
      point
  have matterEquality :
      output.matter point = current.matter point :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
      source current space
  have conjugateMatterEquality :
      output.conjugateMatter point = current.conjugateMatter point :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
      source current space
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at source
      output current point coframeEquality matterEquality
      conjugateMatterEquality
  have spinEquality :
      formNativeMatterSpinThreeForm source 0 point
          (toContinuumPointField output point) =
        formNativeMatterSpinThreeForm source 0 point
          (toContinuumPointField current point) := by
    unfold diracDualFormNativeActionSpinResponseAt
      formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
    exact neg_injective physicalSpinEquality
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [covariantDerivativeEquality, spinEquality]

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_lorentzConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).lorentzConnection =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        InputActual (canonicalCauchySlicePoint 0 space) := by
  have inputSimplicity :
      FormNativeGravitySimplicityEquation InputActual := by
    unfold InputActual FixedP506FormNativeJointActionSolvedSuccessor
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        positiveSmoothUnifiedSource _
  exact
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_lorentzResidual_zeroSlice
      positiveSmoothUnifiedSource InputActual inputSimplicity space

/-- Exact gravity-auxiliary channel of the assembled repaired section.  It is
the literal global/contact curvature seam and remains a diagnostic support
coordinate. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint time space)).gravityAuxiliary =
      holonomicContravariantGravityCurvature SectionActual
          (canonicalCauchySlicePoint time space) -
        holonomicContravariantGravityCurvature
          (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration InputActual space))
          (canonicalCauchySlicePoint time 0) := by
  let contact :=
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration InputActual space)
  have contactZero :
      formNativeGravityAuxiliaryEulerResidual
          (toContinuumPointField contact
            (canonicalCauchySlicePoint time 0)) =
        0 :=
    congrFun
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_auxiliaryEquation
        positiveSmoothUnifiedSource
        (spatiallyRecenterHolonomicConfiguration InputActual space))
      (canonicalCauchySlicePoint time 0)
  change
    holonomicContravariantGravityCurvature SectionActual
          (canonicalCauchySlicePoint time space) -
        gravityInternalDualEquiv
          (SectionActual.gravityAuxiliary
            (canonicalCauchySlicePoint time space)) +
        SectionActual.gravitySimplicityMultiplier
          (canonicalCauchySlicePoint time space) =
      _
  change
    holonomicContravariantGravityCurvature contact
          (canonicalCauchySlicePoint time 0) -
        gravityInternalDualEquiv
          (contact.gravityAuxiliary (canonicalCauchySlicePoint time 0)) +
        contact.gravitySimplicityMultiplier
          (canonicalCauchySlicePoint time 0) =
      0 at contactZero
  dsimp only [SectionActual,
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor]
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_multiplier_slice]
  dsimp only [contact] at contactZero ⊢
  linear_combination contactZero

/-! ## Four-channel checkpoint -/

def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  { fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      point with
    gravityMultiplier := 0
    gravityAuxiliary :=
      holonomicContravariantGravityCurvature SectionActual point -
        holonomicContravariantGravityCurvature
          (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
            positiveSmoothUnifiedSource
            (spatiallyRecenterHolonomicConfiguration InputActual space))
          (canonicalCauchySlicePoint 0 0)
    p286GaugeAuxiliary := 0
    lorentzConnection :=
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        InputActual point }

/-- Same-actual carrier equality for the first four computed channels. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_fourChannelNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
        0 space
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_lorentzConnection_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
