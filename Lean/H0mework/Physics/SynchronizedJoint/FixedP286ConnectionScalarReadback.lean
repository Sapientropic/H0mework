import H0mework.Physics.SynchronizedJoint.FixedP286AuxiliaryReadback
import H0mework.Physics.JointVariation.SectionFixedScalarAssemblyNormalForm
import H0mework.Physics.JointVariation.P286LiveElectricCauchyOperator
import H0mework.Physics.ActionForcing.FixedMotherActionChargeScalarPairing

/-!
# Fixed synchronized Lorentz-path P286-connection/scalar readback

The source/current-only Lorentz-path occurrence has already emitted one
global actual.  This module projects its whole action-jet naturality theorem
to the coupled P286-connection/scalar readers.  The P286 connection reader is
blind to every Lorentz-path seam; the scalar reader sees exactly the scalar
differential-momentum-divergence seam.

Both statements are downstream readouts of the same emitted actual.  No
residual coordinate, support, target field, branch, or zero-fiber witness is
accepted by an action writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286ConnectionScalarReadback

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506ScalarAssemblyNormalForm
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNaturality
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506P286RequiredExteriorDerivativeSpatialRegularity
open StageNineDiracDualFormNativeFixedP506U6MotherActionChargeScalarPairing
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineGlobalIntegratedAction
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineHolonomicField
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286ConnectionReadbackModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286ConnectionReadbackCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor
private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual
private abbrev Constitutive : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor
private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact
    Source Input point

private abbrev MatchingContact (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionMatchingContact point

private abbrev Charge : P286CoordinateCarrier :=
  StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile.fixedP506L0U6OccurrenceP286MotherActionCharge
private abbrev Q : P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

/-! ## Exact whole-section P286 auxiliary seam -/

/-- The global diagonal does not invent a new P286 auxiliary field: after
the source/current origin profile and its canonical time increment are
assembled, the resulting whole field is exactly the solved affine input
field.  The spatial-volume entry of the required profile is deliberately
absent from the time-axis increment and remains a downstream connection
residual support. -/
private theorem raw_gaugeAuxiliaryCoordinate_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate Raw
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate Input
        (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_normalForm,
    canonicalSpatialProjection_slice,
    fixedP506L0RequiredExterior_originAuxiliary_eq_fixedInput,
    completeJointActionMatchingContactPoint, canonicalTimeProjection_slice]
  have sliceZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [sliceZero]
  simp [formNativeP286CanonicalAuxiliaryIncrement]

private theorem input_auxiliaryDirectionalDerivative_eq_constitutive_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative Input
        (canonicalCauchySlicePoint 0 space) direction =
      p286GaugeAuxiliaryDirectionalDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) direction := by
  calc
    p286GaugeAuxiliaryDirectionalDerivative Input
          (canonicalCauchySlicePoint 0 space) direction =
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection direction) := by
      unfold p286GaugeAuxiliaryDirectionalDerivative
        fieldDirectionalDerivative
      have coordinateEq :
          holonomicP286GaugeAuxiliaryCoordinate Input =
            holonomicP286GaugeAuxiliaryCoordinate
              FixedP506JointActionSuccessor := by
        unfold holonomicP286GaugeAuxiliaryCoordinate
        rw [fixedP506FormNativeJointActionSolvedSuccessor_gaugeAuxiliary]
      rw [coordinateEq]
      exact
        fixedP506JointActionSuccessor_auxiliaryDirectionalDerivative_at
          (canonicalCauchySlicePoint 0 space) direction
    _ = p286GaugeAuxiliaryDirectionalDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) direction :=
      (fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative_zeroSlice
        space direction).symm

private theorem input_pureExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Input
        (canonicalCauchySlicePoint 0 space) =
      ![Q,
        0, 0,
        -Q] := by
  have derivativeEq :
      p286GaugeAuxiliaryDirectionalDerivative Input
          (canonicalCauchySlicePoint 0 space) =
        p286GaugeAuxiliaryDirectionalDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) := by
    funext direction
    exact input_auxiliaryDirectionalDerivative_eq_constitutive_zeroSlice
      space direction
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [derivativeEq]
  exact constitutive_pureExterior_zeroSlice_normalForm space

private theorem raw_auxiliarySpatialDirectionalDerivative_eq_input
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286GaugeAuxiliaryDirectionalDerivative Raw
        (canonicalCauchySlicePoint 0 space) direction.succ =
      p286GaugeAuxiliaryDirectionalDerivative Input
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  let rawCoordinate := holonomicP286GaugeAuxiliaryCoordinate Raw
  let inputCoordinate := holonomicP286GaugeAuxiliaryCoordinate Input
  have rawDifferentiable :
      DifferentiableAt ℝ rawCoordinate
        (canonicalCauchySlicePoint 0 space) := by
    apply differentiableAt_pi.2
    intro pair
    apply (differentiableAt_piLp 2).2
    intro coordinate
    exact
      (((contDiff_piLp 2).mp
        (fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_contDiff
          pair)) coordinate).differentiable (by simp) |>.differentiableAt
  have inputDifferentiable :
      DifferentiableAt ℝ inputCoordinate
        (canonicalCauchySlicePoint 0 space) := by
    apply differentiableAt_pi.2
    intro pair
    apply (differentiableAt_piLp 2).2
    intro coordinate
    exact
      (((contDiff_piLp 2).mp
        (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.1
          pair)) coordinate).differentiable (by simp) |>.differentiableAt
  have restrictionEq :
      rawCoordinate ∘ canonicalCauchySlicePoint 0 =
        inputCoordinate ∘ canonicalCauchySlicePoint 0 := by
    funext candidate
    exact raw_gaugeAuxiliaryCoordinate_zeroSlice_eq_input candidate
  calc
    p286GaugeAuxiliaryDirectionalDerivative Raw
          (canonicalCauchySlicePoint 0 space) direction.succ =
        fderiv ℝ (rawCoordinate ∘ canonicalCauchySlicePoint 0) space
          (canonicalSpatialCoordinateDirection direction) :=
      (fderiv_canonicalCauchySlicePoint_spatial_local rawCoordinate 0 space
        direction rawDifferentiable).symm
    _ = fderiv ℝ (inputCoordinate ∘ canonicalCauchySlicePoint 0) space
          (canonicalSpatialCoordinateDirection direction) := by
      rw [restrictionEq]
    _ = p286GaugeAuxiliaryDirectionalDerivative Input
          (canonicalCauchySlicePoint 0 space) direction.succ :=
      fderiv_canonicalCauchySlicePoint_spatial_local inputCoordinate 0 space
        direction inputDifferentiable

private theorem raw_pureExterior_zeroSlice_spatialVolume
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Raw
        (canonicalCauchySlicePoint 0 space) 3 =
      -Q := by
  rw [show
      holonomicP286GaugeAuxiliaryExteriorDerivative Raw
          (canonicalCauchySlicePoint 0 space) 3 =
        holonomicP286GaugeAuxiliaryExteriorDerivative Input
          (canonicalCauchySlicePoint 0 space) 3 by
    unfold holonomicP286GaugeAuxiliaryExteriorDerivative
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
    simp [threeFormFirst, threeFormSecond, threeFormThird]
    have first :
        p286GaugeAuxiliaryDirectionalDerivative Raw
            (canonicalCauchySlicePoint 0 space) 1 3 =
          p286GaugeAuxiliaryDirectionalDerivative Input
            (canonicalCauchySlicePoint 0 space) 1 3 := by
      simpa using congrFun
        (raw_auxiliarySpatialDirectionalDerivative_eq_input space 0) 3
    have second :
        p286GaugeAuxiliaryDirectionalDerivative Raw
            (canonicalCauchySlicePoint 0 space) 2 4 =
          p286GaugeAuxiliaryDirectionalDerivative Input
            (canonicalCauchySlicePoint 0 space) 2 4 := by
      simpa using congrFun
        (raw_auxiliarySpatialDirectionalDerivative_eq_input space 1) 4
    have third :
        p286GaugeAuxiliaryDirectionalDerivative Raw
            (canonicalCauchySlicePoint 0 space) 3 5 =
          p286GaugeAuxiliaryDirectionalDerivative Input
            (canonicalCauchySlicePoint 0 space) 3 5 := by
      simpa using congrFun
        (raw_auxiliarySpatialDirectionalDerivative_eq_input space 2) 5
    rw [first, second, third]]
  exact congrFun (input_pureExterior_zeroSlice_normalForm space) 3

private theorem matchingContact_pureExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (MatchingContact (canonicalCauchySlicePoint 0 space)) 0 =
      ![Q, 0, 0,
        -Q - p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
          Charge] := by
  unfold MatchingContact
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon,
    canonicalSpatialProjection_slice,
    StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm.fixedP506L0FinalCommonActionActual_p286ExteriorDerivative_normalForm,
    final_requiredExteriorDerivative_zeroSlice_normalForm]

private theorem p286GaugeConnection_readout_withCompleteJointSeam_of_scalar_zero
    (point : BasePoint)
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : CompleteJointActionJetAssemblySeam)
    (scalarZero : seam.scalarCovariantDerivative = 0) :
    (diracDualFormNativeJointResidualOfActionJet Source point
      (pointwiseActionJetWithCompleteJointAssemblySeam contactJet seam)
      ).p286GaugeConnection =
      seam.p286GaugeAuxiliaryExteriorCovariantDerivative +
        (diracDualFormNativeJointResidualOfActionJet Source point contactJet
          ).p286GaugeConnection := by
  unfold diracDualFormNativeJointResidualOfActionJet
    pointwiseActionJetWithCompleteJointAssemblySeam
  rw [scalarZero]
  simp only [zero_add]
  abel

private theorem raw_p286GaugeConnectionResidual_zeroSlice_eq_assemblySeam
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Raw
      (canonicalCauchySlicePoint 0 space)).p286GaugeConnection =
      (fixedP506L0CompleteJointActionSpacetimeAssemblySeam
        (canonicalCauchySlicePoint 0 space)
        ).p286GaugeAuxiliaryExteriorCovariantDerivative := by
  let point := canonicalCauchySlicePoint 0 space
  let contactJet := generatedDiracDualFormNativePointwiseActionJet Source
    (MatchingContact point) (completeJointActionMatchingContactPoint point)
  let seam := fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
  have scalarZero : seam.scalarCovariantDerivative = 0 := by
    funext direction
    exact
      fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_zeroSlice
        space direction
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0CompleteJointActionSpacetimeSection_actionJet_naturality,
    p286GaugeConnection_readout_withCompleteJointSeam_of_scalar_zero
      point contactJet seam scalarZero]
  have contactZero :=
    fixedP506L0CompleteJointActionMatchingContact_timeZero_zeroFiber space
  have contactReadZero :
      (diracDualFormNativeJointResidualOfActionJet Source point contactJet
        ).p286GaugeConnection = 0 := by
    rw [diracDualFormNativeJointResidualOfActionJet_point_independent
      Source point (completeJointActionMatchingContactPoint point) contactJet]
    rw [← diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
    exact congrArg
      (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
        residual.p286GaugeConnection)
      contactZero
  rw [contactReadZero, add_zero]

private theorem raw_p286AssemblySeam_zeroSlice_spatialVolume
    (space : StageNineSpatialPoint) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam
      (canonicalCauchySlicePoint 0 space)
      ).p286GaugeAuxiliaryExteriorCovariantDerivative 3 =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) • Charge := by
  let point := canonicalCauchySlicePoint 0 space
  have matchingPoint : completeJointActionMatchingContactPoint point = 0 := by
    rw [show point = canonicalCauchySlicePoint 0 space from rfl,
      completeJointActionMatchingContactPoint, canonicalTimeProjection_slice]
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate Raw point =
        holonomicP286GaugeConnectionCoordinate (MatchingContact point) 0 := by
    unfold holonomicP286GaugeConnectionCoordinate
    change
      (fun direction => p286CoordinateEquiv (Raw.gaugeConnection point direction)) =
        fun direction =>
          p286CoordinateEquiv ((MatchingContact point).gaugeConnection 0 direction)
    funext direction
    rw [show Raw.gaugeConnection point =
        (MatchingContact point).gaugeConnection
          (completeJointActionMatchingContactPoint point) by
      exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at
          Source Input point]
    rw [matchingPoint]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate Raw point =
        holonomicP286GaugeAuxiliaryCoordinate (MatchingContact point) 0 := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    change
      (fun pair => p286CoordinateEquiv (Raw.gaugeAuxiliary point pair)) =
        fun pair =>
          p286CoordinateEquiv ((MatchingContact point).gaugeAuxiliary 0 pair)
    funext pair
    rw [show Raw.gaugeAuxiliary point =
        (MatchingContact point).gaugeAuxiliary
          (completeJointActionMatchingContactPoint point) by
      exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeAuxiliary_at
          Source Input point]
    rw [matchingPoint]
  unfold fixedP506L0CompleteJointActionSpacetimeAssemblySeam
    completeJointActionJetAssemblySeam
  rw [matchingPoint]
  change
    (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Raw point -
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (MatchingContact point) 0) 3 = _
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    connectionEq, auxiliaryEq]
  dsimp only [point]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [raw_pureExterior_zeroSlice_spatialVolume space,
    congrFun (matchingContact_pureExterior_zeroSlice_normalForm space) 3]
  simp

private theorem final_scalar_eq_raw : Final.scalar = Raw.scalar := by
  rfl

private theorem final_matter_eq_raw : Final.matter = Raw.matter := by
  rfl

private theorem final_conjugateMatter_eq_raw :
    Final.conjugateMatter = Raw.conjugateMatter := by
  rfl

private theorem final_coframe_zeroSlice_eq_raw
    (space : StageNineSpatialPoint) :
    Final.coframe (canonicalCauchySlicePoint 0 space) =
      Raw.coframe (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  change
    (1 : LorentzianCoframe) =
      Raw.coframe (canonicalCauchySlicePoint 0 space)
  rw [show Raw.coframe = Input.coframe by
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe
        Source Input]
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
      space).symm

private theorem raw_gaugeConnection_eq_input :
    Raw.gaugeConnection = Input.gaugeConnection := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
      Source Input

private theorem final_gaugeConnection_eq_raw :
    Final.gaugeConnection = Raw.gaugeConnection := by
  calc
    Final.gaugeConnection = Input.gaugeConnection :=
      final_gaugeConnection_eq_input
    _ = Raw.gaugeConnection := raw_gaugeConnection_eq_input.symm

private theorem final_p286AuxiliaryExteriorCovariantDerivative_eq_raw
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Final point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Raw point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [final_gaugeConnection_eq_raw, final_gaugeAuxiliary_eq_raw]

private theorem final_chargedGaugeThreeForm_zeroSlice_eq_raw
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Final
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Raw
          (canonicalCauchySlicePoint 0 space)) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact final_coframe_zeroSlice_eq_raw space
  · exact congrFun final_scalar_eq_raw _
  · unfold holonomicScalarCovariantDerivative
    rw [final_scalar_eq_raw, final_gaugeConnection_eq_raw]
  · exact congrFun final_matter_eq_raw _
  · exact congrFun final_conjugateMatter_eq_raw _

private theorem final_p286GaugeConnectionResidual_zeroSlice_eq_raw
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Final
      (canonicalCauchySlicePoint 0 space)
      ).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual Source Raw
        (canonicalCauchySlicePoint 0 space)
        ).p286GaugeConnection := by
  change
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Final
          (canonicalCauchySlicePoint 0 space) +
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Final
            (canonicalCauchySlicePoint 0 space)) =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Raw
          (canonicalCauchySlicePoint 0 space) +
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Raw
            (canonicalCauchySlicePoint 0 space))
  rw [final_p286AuxiliaryExteriorCovariantDerivative_eq_raw,
    final_chargedGaugeThreeForm_zeroSlice_eq_raw]

/-- On the exact emitted Final actual, the zero-slice spatial-volume P286
connection residual is the complete-joint assembly support.  This is a
read-after-write equation on the same occurrence, not a correction formula. -/
theorem final_p286GaugeConnectionResidual_zeroSlice_spatialVolume
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Final
        (canonicalCauchySlicePoint 0 space)).p286GaugeConnection 3 =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
        Charge := by
  rw [final_p286GaugeConnectionResidual_zeroSlice_eq_raw]
  rw [congrFun
    (raw_p286GaugeConnectionResidual_zeroSlice_eq_assemblySeam space) 3]
  exact raw_p286AssemblySeam_zeroSlice_spatialVolume space

private theorem motherActionCharge_ne_zero : Charge ≠ 0 := by
  intro chargeZero
  change
    fixedP506L0U6OccurrenceP286MotherActionCharge = 0 at chargeZero
  have pairing := motherActionChargeHyperchargeScalarPairing_eq
  unfold motherActionChargeHyperchargeScalarPairing at pairing
  change
    scalarCoordinatePairingRe _
        (scalarP286ActionBilinear
          fixedP506L0U6OccurrenceP286MotherActionCharge _) =
      29 / 54 at pairing
  rw [chargeZero] at pairing
  simp [scalarP286ActionBilinear, scalarCoordinatePairingRe] at pairing
  norm_num at pairing

/-- At the canonical unit spatial occurrence, the exact Final residual reads
back the nonzero mother-action charge itself. -/
theorem final_p286GaugeConnectionResidual_zeroSlice_spatialE0_spatialVolume :
    (diracDualFormNativePointwiseJointResidual Source Final
        (canonicalCauchySlicePoint 0 SpatialE0)).p286GaugeConnection 3 =
      Charge := by
  rw [final_p286GaugeConnectionResidual_zeroSlice_spatialVolume]
  have radius :
      p286SpatialRadiusSquared
          (canonicalCauchySlicePoint 0 SpatialE0) = 1 := by
    simp [SpatialE0, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, p286BaseCoordinate_apply,
      Fin.sum_univ_three]
  rw [radius, one_smul]

/-- The exact P286 connection channel of Final is nonzero at the same
source-owned unit spatial occurrence. -/
theorem final_p286GaugeConnectionResidual_zeroSlice_spatialE0_ne_zero :
    (diracDualFormNativePointwiseJointResidual Source Final
        (canonicalCauchySlicePoint 0 SpatialE0)).p286GaugeConnection ≠ 0 := by
  intro residualZero
  have coordinateZero := congrFun residualZero 3
  rw [final_p286GaugeConnectionResidual_zeroSlice_spatialE0_spatialVolume]
    at coordinateZero
  exact motherActionCharge_ne_zero coordinateZero

/-- Consequently, the exact synchronized Lorentz-path Final actual is not
on the complete pointwise joint zero fiber at this emitted occurrence. -/
theorem final_not_onPointwiseJointZeroFiber_zeroSlice_spatialE0 :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber Source Final
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  intro zeroFiber
  apply final_p286GaugeConnectionResidual_zeroSlice_spatialE0_ne_zero
  unfold OnDiracDualFormNativePointwiseJointZeroFiber at zeroFiber
  have projected := congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection) zeroFiber
  simpa using projected

/-- Public explicit form of the same source-owned unit-spatial obstruction.
This avoids exporting a theorem whose occurrence is hidden behind a private
local abbreviation. -/
theorem final_p286GaugeConnectionResidual_zeroSlice_unitSpatial_ne_zero :
    (diracDualFormNativePointwiseJointResidual Source Final
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
      ).p286GaugeConnection ≠ 0 := by
  simpa [SpatialE0] using
    final_p286GaugeConnectionResidual_zeroSlice_spatialE0_ne_zero

/-- Public complete-zero-fiber counterpart at the same explicit occurrence. -/
theorem final_not_onPointwiseJointZeroFiber_zeroSlice_unitSpatial :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber Source Final
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) := by
  simpa [SpatialE0] using
    final_not_onPointwiseJointZeroFiber_zeroSlice_spatialE0

private theorem
    p286GaugeConnection_readout_withLorentzPathSeam
    (point : BasePoint)
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : LorentzPathActionJetSeam) :
    (diracDualFormNativeJointResidualOfActionJet Source point
      (pointwiseActionJetWithLorentzPathSeam contactJet seam)
      ).p286GaugeConnection =
      (diracDualFormNativeJointResidualOfActionJet Source point contactJet
        ).p286GaugeConnection := by
  rfl

private theorem scalar_readout_withLorentzPathSeam
    (point : BasePoint)
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : LorentzPathActionJetSeam) :
    (diracDualFormNativeJointResidualOfActionJet Source point
      (pointwiseActionJetWithLorentzPathSeam contactJet seam)).scalar =
      (diracDualFormNativeJointResidualOfActionJet Source point contactJet
        ).scalar - seam.scalarDifferentialMomentumDivergence := by
  funext direction
  have algebraicEq :
      pointwiseDiracDualScalarAlgebraicDirectionalCoefficient Source point
          (pointwiseActionJetWithLorentzPathSeam contactJet seam) direction =
        pointwiseDiracDualScalarAlgebraicDirectionalCoefficient Source point
          contactJet direction := by
    rfl
  change _ - (seam.scalarDifferentialMomentumDivergence direction + _) =
    (_ - _) - seam.scalarDifferentialMomentumDivergence direction
  rw [algebraicEq]
  ring

/-- The exact final P286-connection residual is the native synchronized
profile-contact read.  None of the seven Lorentz-path seams enters this
channel. -/
theorem final_p286GaugeConnectionResidual_eq_profileContact
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual Source (Contact point) 0
        ).p286GaugeConnection := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_actionJet_naturality,
    p286GaugeConnection_readout_withLorentzPathSeam]
  rw [diracDualFormNativeJointResidualOfActionJet_point_independent
    Source point 0
    (generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0)]
  exact congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection)
    (diracDualFormNativePointwiseJointResidual_eq_actionJetReadout
      Source (Contact point) 0).symm

/-- The scalar reader of the same final actual differs from the synchronized
profile-contact read by exactly one generated divergence seam.  This is the
complete support equation for the channel, not a correction formula. -/
theorem final_scalarResidual_eq_profileContact_sub_divergenceSeam
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point).scalar =
      (diracDualFormNativePointwiseJointResidual Source (Contact point) 0
        ).scalar -
      (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
        point).scalarDifferentialMomentumDivergence := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_actionJet_naturality,
    scalar_readout_withLorentzPathSeam]
  rw [diracDualFormNativeJointResidualOfActionJet_point_independent
    Source point 0
    (generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0)]
  rw [← diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
  rfl

/-- Grouped projection of the two coupled readers from the single whole-jet
naturality theorem. -/
theorem final_p286GaugeConnection_scalarResidual_pair_normalForm
    (point : BasePoint) :
    ((diracDualFormNativePointwiseJointResidual Source Final point
        ).p286GaugeConnection,
      (diracDualFormNativePointwiseJointResidual Source Final point).scalar) =
      ((diracDualFormNativePointwiseJointResidual Source (Contact point) 0
          ).p286GaugeConnection,
        (diracDualFormNativePointwiseJointResidual Source (Contact point) 0
          ).scalar -
        (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
          point).scalarDifferentialMomentumDivergence) := by
  rw [final_p286GaugeConnectionResidual_eq_profileContact,
    final_scalarResidual_eq_profileContact_sub_divergenceSeam]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286ConnectionScalarReadback
