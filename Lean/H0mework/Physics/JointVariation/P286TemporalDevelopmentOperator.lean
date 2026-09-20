import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.GaugeAction.P286CompleteActionResponseOperator
import H0mework.Physics.GaugeAction.P286GaugeYangMillsReadout
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Global temporal P286 development of the complete joint action

The complete-joint profile generates, at every spacetime occurrence, both
the P286 auxiliary value and the pure exterior derivative required by the
mother-action connection equation.  This module turns that pointwise data
into one four-dimensional auxiliary field:

* the action-generated time-zero values form the canonical spatial anchor;
* the already assembled exterior derivative of that anchor is read on the
  same current;
* the three temporal components of the remaining action requirement are
  integrated along the canonical time line.

The constructor consumes only `(source,current)`.  No residual, support
coordinate, correction value, branch, boundary constant, or equation receipt
is an input.  The purely spatial `123` component and equality with the
occurrence-by-occurrence algebraic auxiliary remain downstream compatibility
readouts of the one generated field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Interval

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286TemporalDevelopmentModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286TemporalDevelopmentCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev CompleteProfiles
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    CompleteJointGeneratedProfiles :=
  sourceActionGeneratedDiracDualCompleteJointProfiles source current point

/-! ## Source/current-only temporal homotopy -/

/-- The action-generated auxiliary value on the canonical zero slice. -/
def completeJointP286ZeroSliceAnchor
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) : P286GaugeTwoForm :=
  (CompleteProfiles source current
    (canonicalCauchySlicePoint 0 space)).p286AuxiliaryOrigin

private theorem fullyRecenterHolonomicConfiguration_gaugeCurvature_origin'
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      holonomicGaugeCurvature current contact := by
  have derivativeEq
      (derivativeDirection formDirection : LorentzianIndex) :
      p286ConnectionDerivative
          (fullyRecenterHolonomicConfiguration current contact) 0
          derivativeDirection formDirection =
        p286ConnectionDerivative current contact derivativeDirection
          formDirection := by
    unfold p286ConnectionDerivative
    apply congrArg p286CoordinateEquiv.symm
    change
      fieldDirectionalDerivative
          ((fun point =>
            holonomicP286GaugeConnectionCoordinate current point
              formDirection) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeConnectionCoordinate current point
              formDirection)
          contact derivativeDirection
    simpa using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point =>
          holonomicP286GaugeConnectionCoordinate current point formDirection)
        contact 0 derivativeDirection
  funext pair
  unfold holonomicGaugeCurvature
  rw [derivativeEq, derivativeEq]
  simp [fullyRecenterHolonomicConfiguration]

private theorem fderiv_canonicalCauchySlicePoint_spatial'
    {V : Type*}
    [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (field : BasePoint → V)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection derivativeDirection) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space)
        derivativeDirection.succ := by
  have derivative :=
    differentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- When the supplied current is already the action-owned constitutive
readout, the occurrence profile's zero-slice anchor is its literal value at
that occurrence.  Thus the temporal development starts from the algebraic
producer itself rather than from an independently supplied boundary datum. -/
@[simp] theorem completeJointP286ZeroSliceAnchor_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    completeJointP286ZeroSliceAnchor source
        (formNativeP286GaugeConstitutiveReadout source configuration) space =
      holonomicP286GaugeAuxiliaryCoordinate
        (formNativeP286GaugeConstitutiveReadout source configuration)
        (canonicalCauchySlicePoint 0 space) := by
  funext pair
  change
    (sourceActionGeneratedDiracDualCompleteJointProfiles source
      (formNativeP286GaugeConstitutiveReadout source configuration)
      (canonicalCauchySlicePoint 0 space)).p286AuxiliaryOrigin pair =
        _
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_p286AuxiliaryOrigin]
  unfold currentP286OriginAuxiliaryCoordinate
  unfold completeJointScalarSecondJetCurrent
  rw [genericDiracDualScalarSecondJetActionResponse_gaugeAuxiliary]
  unfold completeJointRepairedConstitutiveCurrent
  unfold completeJointGeneratedProfileRestartCurrent
  change
    p286CoordinateEquiv
        (diracDualFormNativeConstitutiveAuxiliaryField source
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
            (fullyRecenterHolonomicConfiguration
              (formNativeP286GaugeConstitutiveReadout source configuration)
              (canonicalCauchySlicePoint 0 space)))
          0 pair) =
      _
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      (fullyRecenterHolonomicConfiguration
        (formNativeP286GaugeConstitutiveReadout source configuration)
        (canonicalCauchySlicePoint 0 space)))
    (fullyRecenterHolonomicConfiguration
      (formNativeP286GaugeConstitutiveReadout source configuration)
      (canonicalCauchySlicePoint 0 space))
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
      source
      (fullyRecenterHolonomicConfiguration
        (formNativeP286GaugeConstitutiveReadout source configuration)
        (canonicalCauchySlicePoint 0 space)))
    0]
  rw [fullyRecenterHolonomicConfiguration_gaugeCurvature_origin']
  rfl

/-- Install the zero-slice action anchor as a time-independent whole field.
Every non-P286-auxiliary field is preserved from the supplied current, so a
dependency-ordered caller can apply this leg after its earlier action writes
without replaying them. -/
def completeJointP286ZeroSliceAnchoredCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (completeJointP286ZeroSliceAnchor source current
          (canonicalSpatialProjection point) pair) }

/-- The pure exterior derivative required by the same occurrence-native
mother action. -/
def completeJointP286RequiredExteriorProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeThreeForm :=
  (CompleteProfiles source current point).p286RequiredExteriorDerivative

/-- The three temporal components not already supplied by the zero-slice
anchor.  The canonical P286 right inverse makes coordinates `01`, `02`, and
`03` identically zero and writes only `23`, `31`, and `12`. -/
def completeJointP286TemporalCorrectionProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
    (completeJointP286RequiredExteriorProfile source current point -
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source current) point)
    canonicalLorentzianTimeDirection

/-- Canonical temporal primitive of each faithful P286 two-form coordinate. -/
def completeJointP286TemporalCorrectionPrimitive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  fun pair =>
    canonicalTimePrimitive
      (fun candidate =>
        completeJointP286TemporalCorrectionProfile source current
          candidate pair)
      point

/-- One branch-free global P286 temporal development.

All non-P286-auxiliary fields are inherited from the supplied current.  The
P286 field is anchored by the action-generated zero slice and advanced by the
same source/current action profile. -/
def sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { completeJointP286ZeroSliceAnchoredCurrent source current with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (completeJointP286ZeroSliceAnchor source current
            (canonicalSpatialProjection point) pair +
          completeJointP286TemporalCorrectionPrimitive source current
            point pair) }

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
      source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
      source current).gaugeConnection =
      current.gaugeConnection :=
  rfl

/-! ## Generated anchor and temporal derivative -/

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_gaugeAuxiliary_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      completeJointP286ZeroSliceAnchor source current space := by
  funext pair
  simp [
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286TemporalCorrectionPrimitive]

/-- The zero time-bound makes the temporal primitive vanish on the entire
Cauchy slice, so every spatial first jet on that slice is inherited from the
action-generated anchor. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_spatialDirectionalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (pair : Fin 6)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current))
        (canonicalCauchySlicePoint 0 space))
    (anchorCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current))
        (canonicalCauchySlicePoint 0 space)) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current)
      (canonicalCauchySlicePoint 0 space) direction.succ) pair =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source current)
        (canonicalCauchySlicePoint 0 space) direction.succ) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current)
  let anchorCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286ZeroSliceAnchoredCurrent source current)
  change
    (fieldDirectionalDerivative finalCoordinate
      (canonicalCauchySlicePoint 0 space) direction.succ) pair =
      (fieldDirectionalDerivative anchorCoordinate
        (canonicalCauchySlicePoint 0 space) direction.succ) pair
  rw [← fderiv_canonicalCauchySlicePoint_spatial' finalCoordinate 0 space
      direction finalCoordinateDifferentiableAt,
    ← fderiv_canonicalCauchySlicePoint_spatial' anchorCoordinate 0 space
      direction anchorCoordinateDifferentiableAt]
  have sliceEquality :
      finalCoordinate ∘ canonicalCauchySlicePoint 0 =
        anchorCoordinate ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    change
      holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)
          (canonicalCauchySlicePoint 0 candidateSpace) =
        holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current)
          (canonicalCauchySlicePoint 0 candidateSpace)
    rw [
      sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_gaugeAuxiliary_zeroSlice]
    funext candidatePair
    simp [completeJointP286ZeroSliceAnchoredCurrent,
      holonomicP286GaugeAuxiliaryCoordinate]
  rw [sliceEquality]

/-- Consequently the purely spatial `123` exterior coordinate at time zero
is exactly the exterior coordinate of the same generated anchor current. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_spatial_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current))
        (canonicalCauchySlicePoint 0 space))
    (anchorCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current))
        (canonicalCauchySlicePoint 0 space)) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source current)
        (canonicalCauchySlicePoint 0 space) 3 := by
  simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    threeFormFirst, threeFormSecond, threeFormThird,
    orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
    orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
  have first :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 1) 3 =
        (p286GaugeAuxiliaryDirectionalDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current)
          (canonicalCauchySlicePoint 0 space) 1) 3 := by
    simpa using
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_spatialDirectionalDerivative_zeroSlice
        source current space 0 3 finalCoordinateDifferentiableAt
        anchorCoordinateDifferentiableAt)
  have second :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 2) 4 =
        (p286GaugeAuxiliaryDirectionalDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current)
          (canonicalCauchySlicePoint 0 space) 2) 4 := by
    simpa using
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_spatialDirectionalDerivative_zeroSlice
        source current space 1 4 finalCoordinateDifferentiableAt
        anchorCoordinateDifferentiableAt)
  have third :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 3) 5 =
        (p286GaugeAuxiliaryDirectionalDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current)
          (canonicalCauchySlicePoint 0 space) 3) 5 := by
    simpa using
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_spatialDirectionalDerivative_zeroSlice
        source current space 2 5 finalCoordinateDifferentiableAt
        anchorCoordinateDifferentiableAt)
  rw [first, second, third]

@[simp] theorem completeJointP286TemporalCorrectionProfile_zeroOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 0 = 0 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem completeJointP286TemporalCorrectionProfile_zeroTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 1 = 0 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem completeJointP286TemporalCorrectionProfile_zeroThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 2 = 0 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem completeJointP286TemporalCorrectionProfile_twoThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 3 =
      (completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current) point) 2 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem completeJointP286TemporalCorrectionProfile_threeOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 4 =
      -(completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current) point) 1 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem completeJointP286TemporalCorrectionProfile_oneTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286TemporalCorrectionProfile source current point 5 =
      (completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286ZeroSliceAnchoredCurrent source current) point) 0 := by
  simp [completeJointP286TemporalCorrectionProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

/-- The temporal homotopy never changes the `01` coordinate. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current) point 0 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286ZeroSliceAnchoredCurrent source current) point 0 := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
    completeJointP286ZeroSliceAnchoredCurrent,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286TemporalCorrectionPrimitive,
    canonicalTimePrimitive]

/-- The temporal homotopy never changes the `02` coordinate. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current) point 1 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286ZeroSliceAnchoredCurrent source current) point 1 := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
    completeJointP286ZeroSliceAnchoredCurrent,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286TemporalCorrectionPrimitive,
    canonicalTimePrimitive]

/-- The temporal homotopy never changes the `03` coordinate. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current) point 2 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286ZeroSliceAnchoredCurrent source current) point 2 := by
  simp [
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
    completeJointP286ZeroSliceAnchoredCurrent,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286TemporalCorrectionPrimitive,
    canonicalTimePrimitive]

/-- Each faithful auxiliary coordinate realizes the source/action-generated
temporal correction.  Analytic hypotheses validate the integral at the
selected point; they do not enter the producer. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_timeLine_hasDerivAt_of_intervalIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (correctionIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        time) :
    NormedHasDerivAt
      (fun candidateTime =>
        p286CoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current).gaugeAuxiliary
            (canonicalCauchySlicePoint candidateTime space) pair))
      (completeJointP286TemporalCorrectionProfile source current
        (canonicalCauchySlicePoint time space) pair)
      time := by
  have primitiveDerivative :=
    canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
      (fun point =>
        completeJointP286TemporalCorrectionProfile source current point pair)
      space time correctionIntervalIntegrable correctionMeasurableAt
      correctionContinuousAt
  have total :=
    (hasDerivAt_const time
      (completeJointP286ZeroSliceAnchor source current space pair)
      ).add primitiveDerivative
  convert total using 1
  · funext candidateTime
    simp only [
      sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
      completeJointP286TemporalCorrectionPrimitive,
      canonicalSpatialProjection_slice,
      Pi.add_apply,
      p286CoordinateEquiv.apply_symm_apply]
  · simp

/-- The actual holonomic time row of the generated auxiliary field is the
same correction differentiated above.  Smoothness is a downstream analytic
validation of the constructed field, not a constructor input. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_temporalDirectionalDerivative_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (finalCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)))
    (correctionIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        time) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current)
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair =
        completeJointP286TemporalCorrectionProfile source current
          (canonicalCauchySlicePoint time space) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current)
  change
    (fieldDirectionalDerivative finalCoordinate
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair = _
  rw [fieldDirectionalDerivative_pi_apply finalCoordinate finalCoordinateSmooth
    (canonicalCauchySlicePoint time space)
    canonicalLorentzianTimeDirection pair]
  have actualDerivative :=
    field_timeLine_hasDerivAt
      (fun point => finalCoordinate point pair) space time
      (((contDiff_pi.mp finalCoordinateSmooth pair).differentiable (by simp)
        ).differentiableAt)
  have generatedDerivative :=
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_timeLine_hasDerivAt_of_intervalIntegrable
      source current space time pair correctionIntervalIntegrable
      correctionMeasurableAt correctionContinuousAt
  exact actualDerivative.unique generatedDerivative

/-- Spatial derivatives of the three electric two-form coordinates are
preserved because the temporal homotopy has literal zero support there. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_electricDirectionalDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (pair : Fin 6)
    (electric : pair = 0 ∨ pair = 1 ∨ pair = 2)
    (finalCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)))
    (anchorCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current))) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current) point direction) pair =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source current)
        point direction) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
        source current)
  let anchorCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286ZeroSliceAnchoredCurrent source current)
  change
    (fieldDirectionalDerivative finalCoordinate point direction) pair =
      (fieldDirectionalDerivative anchorCoordinate point direction) pair
  rw [fieldDirectionalDerivative_pi_apply finalCoordinate finalCoordinateSmooth
    point direction pair]
  rw [fieldDirectionalDerivative_pi_apply anchorCoordinate
    anchorCoordinateSmooth point direction pair]
  have componentEquality :
      (fun candidate => finalCoordinate candidate pair) =
        fun candidate => anchorCoordinate candidate pair := by
    funext candidate
    rcases electric with first | second | third
    · subst pair
      exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroOne
          source current candidate
    · subst pair
      exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroTwo
          source current candidate
    · subst pair
      exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_coordinate_zeroThree
          source current candidate
  rw [componentEquality]

/-- The zero-slice anchor is constant along every canonical time line. -/
theorem completeJointP286ZeroSliceAnchoredCurrent_temporalDirectionalDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (anchorCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current))) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (completeJointP286ZeroSliceAnchoredCurrent source current)
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair =
      0 := by
  let anchorCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286ZeroSliceAnchoredCurrent source current)
  change
    (fieldDirectionalDerivative anchorCoordinate
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair = 0
  rw [fieldDirectionalDerivative_pi_apply anchorCoordinate
    anchorCoordinateSmooth (canonicalCauchySlicePoint time space)
    canonicalLorentzianTimeDirection pair]
  have actualDerivative :=
    field_timeLine_hasDerivAt
      (fun point => anchorCoordinate point pair) space time
      (((contDiff_pi.mp anchorCoordinateSmooth pair).differentiable (by simp)
        ).differentiableAt)
  have constantDerivative :
      NormedHasDerivAt
        (fun _ : ℝ =>
          completeJointP286ZeroSliceAnchor source current space pair)
        0 time :=
    hasDerivAt_const time _
  have lineEquality :
      (fun candidateTime =>
        anchorCoordinate
          (canonicalCauchySlicePoint candidateTime space) pair) =
        fun _ : ℝ =>
          completeJointP286ZeroSliceAnchor source current space pair := by
    funext candidateTime
    simp [anchorCoordinate, completeJointP286ZeroSliceAnchoredCurrent,
      holonomicP286GaugeAuxiliaryCoordinate]
  rw [lineEquality] at actualDerivative
  exact actualDerivative.unique constantDerivative

/-- The single global temporal development realizes all three action-required
three-form components that contain the canonical time direction.  Coordinate
`123` is intentionally excluded: it is the remaining spatial/Gauss
compatibility of this same generated field. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (triple : Fin 4)
    (temporal : triple ≠ 3)
    (finalCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)))
    (anchorCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current)))
    (correctionIntervalIntegrable :
      ∀ pair : Fin 6,
        IntervalIntegrable
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ∀ pair : Fin 6,
        ContinuousAt
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          time) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint time space) triple =
      completeJointP286RequiredExteriorProfile source current
        (canonicalCauchySlicePoint time space) triple := by
  have temporalDerivative (pair : Fin 6) :=
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_temporalDirectionalDerivative_apply
      source current space time pair finalCoordinateSmooth
      (correctionIntervalIntegrable pair) (correctionMeasurableAt pair)
      (correctionContinuousAt pair)
  have temporalDerivativeZero (pair : Fin 6) :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint time space) 0) pair =
          completeJointP286TemporalCorrectionProfile source current
            (canonicalCauchySlicePoint time space) pair := by
    simpa [canonicalLorentzianTimeDirection] using temporalDerivative pair
  have electricDerivative
      (direction : LorentzianIndex)
      (pair : Fin 6)
      (electric : pair = 0 ∨ pair = 1 ∨ pair = 2) :=
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_electricDirectionalDerivative
      source current (canonicalCauchySlicePoint time space) direction pair
      electric finalCoordinateSmooth anchorCoordinateSmooth
  have anchorTemporalDerivative (pair : Fin 6) :=
    completeJointP286ZeroSliceAnchoredCurrent_temporalDirectionalDerivative
      source current space time pair anchorCoordinateSmooth
  have anchorTemporalDerivativeZero (pair : Fin 6) :
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286ZeroSliceAnchoredCurrent source current)
        (canonicalCauchySlicePoint time space) 0) pair =
          0 := by
    simpa [canonicalLorentzianTimeDirection] using
      anchorTemporalDerivative pair
  fin_cases triple
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 5]
    rw [electricDerivative 1 1 (Or.inr (Or.inl rfl))]
    rw [electricDerivative 2 0 (Or.inl rfl)]
    rw [completeJointP286TemporalCorrectionProfile_oneTwo]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      anchorTemporalDerivativeZero]
    abel
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 4]
    rw [electricDerivative 1 2 (Or.inr (Or.inr rfl))]
    rw [electricDerivative 3 0 (Or.inl rfl)]
    rw [completeJointP286TemporalCorrectionProfile_threeOne]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      anchorTemporalDerivativeZero]
    abel
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 3]
    rw [electricDerivative 2 2 (Or.inr (Or.inr rfl))]
    rw [electricDerivative 3 1 (Or.inr (Or.inl rfl))]
    rw [completeJointP286TemporalCorrectionProfile_twoThree]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      anchorTemporalDerivativeZero]
    abel
  · exact (temporal rfl).elim

/-- Exact boundary of the temporal producer: after the three generated
temporal coordinates have been realized, full pure-exterior closure is
equivalent to the single spatial `123` compatibility on the same actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_fullExteriorDerivative_iff_spatial
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (finalCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)))
    (anchorCoordinateSmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent source current)))
    (correctionIntervalIntegrable :
      ∀ pair : Fin 6,
        IntervalIntegrable
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          MeasureTheory.volume 0 time)
    (correctionMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          (nhds time) MeasureTheory.volume)
    (correctionContinuousAt :
      ∀ pair : Fin 6,
        ContinuousAt
          (fun candidateTime =>
            completeJointP286TemporalCorrectionProfile source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          time) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint time space) =
        completeJointP286RequiredExteriorProfile source current
          (canonicalCauchySlicePoint time space) ↔
      holonomicP286GaugeAuxiliaryExteriorDerivative
          (sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
            source current)
          (canonicalCauchySlicePoint time space) 3 =
        completeJointP286RequiredExteriorProfile source current
          (canonicalCauchySlicePoint time space) 3 := by
  constructor
  · intro equality
    exact congrFun equality 3
  · intro spatial
    funext triple
    fin_cases triple
    · exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
          source current space time 0 (by decide) finalCoordinateSmooth
          anchorCoordinateSmooth correctionIntervalIntegrable
          correctionMeasurableAt correctionContinuousAt
    · exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
          source current space time 1 (by decide) finalCoordinateSmooth
          anchorCoordinateSmooth correctionIntervalIntegrable
          correctionMeasurableAt correctionContinuousAt
    · exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
          source current space time 2 (by decide) finalCoordinateSmooth
          anchorCoordinateSmooth correctionIntervalIntegrable
          correctionMeasurableAt correctionContinuousAt
    · exact spatial

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
