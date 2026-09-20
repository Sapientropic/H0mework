import H0mework.Physics.JointVariation.P286RequiredExteriorProfileNaturality
import H0mework.Physics.DualVariation.JointResidualCarrier

/-!
# Complete-joint P286 live-electric Cauchy operator

The complete-joint occurrence profile can be assembled pointwise into one
global value/jet carrier.  Both components are generated from the same
`(source,current)`:

* the first component is the occurrence-native constitutive auxiliary value;
* the second component is the occurrence-native exterior derivative required
  by the mother action.

For a current already produced by the constitutive readout, the first
component is its literal all-point auxiliary field and the second component
is its literal direct all-point action read.  The remaining question is the
holonomicity of this generated pair, not the construction of another contact
family and not a residual-built correction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
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

private theorem fieldDirectionalDerivative_pi_apply_of_differentiableAt
    {I V : Type*}
    [Fintype I]
    [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (index : I)
    (fieldDifferentiableAt : DifferentiableAt ℝ field point) :
    (fieldDirectionalDerivative field point direction) index =
      fieldDirectionalDerivative (fun candidate => field candidate index)
        point direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

theorem fderiv_canonicalCauchySlicePoint_spatial_local
    {V : Type*}
    [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (field : BasePoint → V)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (fieldDifferentiableAt :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection direction) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space) direction.succ := by
  have derivative :=
    fieldDifferentiableAt.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-! ## One global source/current-owned value/jet carrier -/

/-- The two P286 data generated at every occurrence, assembled as one global
carrier rather than retained as a family of contact objects. -/
def completeJointP286FullOccurrenceGlobalActionJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → P286GaugeTwoForm × P286GaugeThreeForm :=
  fun point =>
    let profile :=
      sourceActionGeneratedDiracDualCompleteJointProfiles source current point
    (profile.p286AuxiliaryOrigin, profile.p286RequiredExteriorDerivative)

/-- Install the generated value component as one global P286 auxiliary field.
The constructor consumes only `(source,current)` and does not accept a jet
compatibility proof or residual coordinate. -/
def completeJointP286FullOccurrenceGlobalAuxiliaryOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        ((completeJointP286FullOccurrenceGlobalActionJet source current point
          ).1 pair) }

/-! ## Positive all-point identification on a constitutive producer -/

private theorem fullyRecenter_gaugeCurvature_origin_total
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

theorem
    completeJointP286FullOccurrenceGlobalActionJet_value_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointP286FullOccurrenceGlobalActionJet source
        (formNativeP286GaugeConstitutiveReadout source configuration) point
      ).1 =
      holonomicP286GaugeAuxiliaryCoordinate
        (formNativeP286GaugeConstitutiveReadout source configuration) point := by
  funext pair
  change
    p286CoordinateEquiv
        (diracDualFormNativeConstitutiveAuxiliaryField source
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
            (fullyRecenterHolonomicConfiguration
              (formNativeP286GaugeConstitutiveReadout source configuration)
              point))
          0 pair) =
      p286CoordinateEquiv
        ((formNativeP286GaugeConstitutiveReadout source configuration
          ).gaugeAuxiliary point pair)
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      (fullyRecenterHolonomicConfiguration
        (formNativeP286GaugeConstitutiveReadout source configuration) point))
    (fullyRecenterHolonomicConfiguration
      (formNativeP286GaugeConstitutiveReadout source configuration) point)
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
      source
      (fullyRecenterHolonomicConfiguration
        (formNativeP286GaugeConstitutiveReadout source configuration) point))
    0]
  rw [fullyRecenter_gaugeCurvature_origin_total]
  rfl

theorem
    completeJointP286FullOccurrenceGlobalActionJet_required_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointP286FullOccurrenceGlobalActionJet source
        (formNativeP286GaugeConstitutiveReadout source configuration) point
      ).2 =
      pointwiseDirectP286RequiredExteriorDerivative source
        (formNativeP286GaugeConstitutiveReadout source configuration) point := by
  exact
    completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
      source (formNativeP286GaugeConstitutiveReadout source configuration)
      point rfl

/-- The full-occurrence mouth therefore supplies both the literal global
constitutive value and the literal global action target on one carrier. -/
theorem
    completeJointP286FullOccurrenceGlobalActionJet_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286FullOccurrenceGlobalActionJet source
        (formNativeP286GaugeConstitutiveReadout source configuration) point =
      (holonomicP286GaugeAuxiliaryCoordinate
          (formNativeP286GaugeConstitutiveReadout source configuration) point,
        pointwiseDirectP286RequiredExteriorDerivative source
          (formNativeP286GaugeConstitutiveReadout source configuration)
          point) := by
  apply Prod.ext
  · exact
      completeJointP286FullOccurrenceGlobalActionJet_value_constitutiveReadout
        source configuration point
  · exact
      completeJointP286FullOccurrenceGlobalActionJet_required_constitutiveReadout
        source configuration point

theorem
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator_gaugeAuxiliary_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (completeJointP286FullOccurrenceGlobalAuxiliaryOperator source
      (formNativeP286GaugeConstitutiveReadout source configuration)
      ).gaugeAuxiliary =
      (formNativeP286GaugeConstitutiveReadout source configuration
        ).gaugeAuxiliary := by
  funext point pair
  apply p286CoordinateEquiv.injective
  change
    p286CoordinateEquiv
        (p286CoordinateEquiv.symm
          ((completeJointP286FullOccurrenceGlobalActionJet source
            (formNativeP286GaugeConstitutiveReadout source configuration)
            point).1 pair)) =
      holonomicP286GaugeAuxiliaryCoordinate
        (formNativeP286GaugeConstitutiveReadout source configuration) point
        pair
  rw [p286CoordinateEquiv.apply_symm_apply]
  exact congrFun
    (completeJointP286FullOccurrenceGlobalActionJet_value_constitutiveReadout
      source configuration point) pair

/-- Consequently the occurrence-native value assembler is a genuine single
global operator and is extensionally the identity on an already generated
constitutive current. -/
theorem
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator source
        (formNativeP286GaugeConstitutiveReadout source configuration) =
      formNativeP286GaugeConstitutiveReadout source configuration := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  exact
    completeJointP286FullOccurrenceGlobalAuxiliaryOperator_gaugeAuxiliary_constitutiveReadout
      source configuration

/-! ## Live-electric Cauchy base and action-owned temporal producer -/

/-- The electric projection in the fixed P286 coordinate order
`(01,02,03,23,31,12)`. -/
def p286ElectricProjection
    (form : P286GaugeTwoForm) : P286GaugeTwoForm :=
  ![form 0, form 1, form 2, 0, 0, 0]

/-- The complementary magnetic projection. -/
def p286MagneticProjection
    (form : P286GaugeTwoForm) : P286GaugeTwoForm :=
  ![0, 0, 0, form 3, form 4, form 5]

/-- Cauchy base for the complete P286 connection write.

The electric coordinates remain the live all-point occurrence read of
`current`.  Only the magnetic coordinates are anchored to the
source/action-generated zero slice.  No residual coordinate or branch
choice enters this definition. -/
def completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  p286ElectricProjection
      (holonomicP286GaugeAuxiliaryCoordinate current point) +
    p286MagneticProjection
      (completeJointP286ZeroSliceAnchor source current
        (canonicalSpatialProjection point))

/-- Install the live-electric Cauchy base as one spacetime configuration. -/
def completeJointP286LiveElectricZeroSliceMagneticBase
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
          source current point pair) }

theorem
    completeJointP286LiveElectricZeroSliceMagneticBase_coordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point =
      completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
        source current point := by
  funext pair
  simp [completeJointP286LiveElectricZeroSliceMagneticBase,
    holonomicP286GaugeAuxiliaryCoordinate]

/-- The base keeps every live electric coordinate at every occurrence. -/
theorem
    completeJointP286LiveElectricZeroSliceMagneticBase_electric
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (pair : Fin 6)
    (electric : pair = 0 ∨ pair = 1 ∨ pair = 2) :
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point pair =
      holonomicP286GaugeAuxiliaryCoordinate current point pair := by
  rw [congrFun
    (completeJointP286LiveElectricZeroSliceMagneticBase_coordinate
      source current point) pair]
  rcases electric with first | second | third <;>
    subst pair <;>
    simp [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection]

/-- The base magnetic coordinates are the action-generated zero-slice
anchor, held constant along each canonical time line. -/
theorem
    completeJointP286LiveElectricZeroSliceMagneticBase_magnetic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (pair : Fin 6)
    (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point pair =
      completeJointP286ZeroSliceAnchor source current
        (canonicalSpatialProjection point) pair := by
  rw [congrFun
    (completeJointP286LiveElectricZeroSliceMagneticBase_coordinate
      source current point) pair]
  rcases magnetic with first | second | third <;>
    subst pair <;>
    simp [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
      p286ElectricProjection, p286MagneticProjection]

/-- The temporal action-write profile for the live-electric Cauchy base.

It is generated from the same occurrence-native required exterior profile
and the exterior derivative of the source/current-owned base.  This is the
connection-action leg; it does not consume a residual carrier. -/
def completeJointP286LiveElectricActionTemporalWriteProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
    (completeJointP286RequiredExteriorProfile source current point -
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point)
    canonicalLorentzianTimeDirection

/-- Canonical time primitive of the action-owned live-electric profile. -/
def completeJointP286LiveElectricActionTemporalWritePrimitive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  fun pair =>
    canonicalTimePrimitive
      (fun candidate =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          source current candidate pair)
      point

/-- Branch-free complete P286 Cauchy producer.

The constructor consumes only the same `(source,current)`: it preserves the
live electric carrier and generates the magnetic temporal primitive from the
mother-action required exterior profile. -/
def sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { completeJointP286LiveElectricZeroSliceMagneticBase source current with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
            source current point pair +
          completeJointP286LiveElectricActionTemporalWritePrimitive
            source current point pair) }

/-- The live-electric P286 leg changes only the auxiliary field, which is not
read by the scalar Euler coefficient. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_scalarResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).scalar =
      (diracDualFormNativePointwiseJointResidual source current point).scalar :=
  rfl

/-- The same auxiliary-only write is silent for the primal-matter Euler
reader. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_matterResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).matter =
      (diracDualFormNativePointwiseJointResidual source current point).matter :=
  rfl

/-- The auxiliary-only write is likewise silent for the adjoint-matter Euler
reader. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_conjugateMatterResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual source current point
        ).conjugateMatter :=
  rfl

theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current) point =
      completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
          source current point +
        completeJointP286LiveElectricActionTemporalWritePrimitive
          source current point := by
  funext pair
  simp [sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
    holonomicP286GaugeAuxiliaryCoordinate]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_zeroOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 0 = 0 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_zeroTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 1 = 0 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_zeroThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 2 = 0 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_twoThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 3 =
      (completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286LiveElectricZeroSliceMagneticBase source current)
          point) 2 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_threeOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 4 =
      -(completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286LiveElectricZeroSliceMagneticBase source current)
          point) 1 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    completeJointP286LiveElectricActionTemporalWriteProfile_oneTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        source current point 5 =
      (completeJointP286RequiredExteriorProfile source current point -
        holonomicP286GaugeAuxiliaryExteriorDerivative
          (completeJointP286LiveElectricZeroSliceMagneticBase source current)
          point) 0 := by
  simp [completeJointP286LiveElectricActionTemporalWriteProfile,
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
    canonicalLorentzianTimeDirection]

@[simp] theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroOne
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current) point 0 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point 0 := by
  simp [sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
    completeJointP286LiveElectricZeroSliceMagneticBase,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286LiveElectricActionTemporalWritePrimitive,
    canonicalTimePrimitive]

@[simp] theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroTwo
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current) point 1 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point 1 := by
  simp [sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
    completeJointP286LiveElectricZeroSliceMagneticBase,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286LiveElectricActionTemporalWritePrimitive,
    canonicalTimePrimitive]

@[simp] theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroThree
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current) point 2 =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point 2 := by
  simp [sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
    completeJointP286LiveElectricZeroSliceMagneticBase,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286LiveElectricActionTemporalWritePrimitive,
    canonicalTimePrimitive]

/-- The canonical primitive realizes the action-owned magnetic time row.
The regularity premises validate the already generated integral and are not
inputs to the producer. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_timeLine_hasDerivAt_of_intervalIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5)
    (profileIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        MeasureTheory.volume 0 time)
    (profileMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        (nhds time) MeasureTheory.volume)
    (profileContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        time) :
    NormedHasDerivAt
      (fun candidateTime =>
        p286CoordinateEquiv
          ((sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current).gaugeAuxiliary
            (canonicalCauchySlicePoint candidateTime space) pair))
      (completeJointP286LiveElectricActionTemporalWriteProfile source current
        (canonicalCauchySlicePoint time space) pair)
      time := by
  have primitiveDerivative :=
    canonicalTimePrimitive_timeLine_hasDerivAt_of_intervalIntegrable
      (fun point =>
        completeJointP286LiveElectricActionTemporalWriteProfile
          source current point pair)
      space time profileIntervalIntegrable profileMeasurableAt
      profileContinuousAt
  have baseDerivative :
      NormedHasDerivAt
        (fun _ : ℝ =>
          completeJointP286ZeroSliceAnchor source current space pair)
        0 time :=
    hasDerivAt_const time _
  have total := baseDerivative.add primitiveDerivative
  convert total using 1
  · funext candidateTime
    simp only [
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
      completeJointP286LiveElectricActionTemporalWritePrimitive,
      Pi.add_apply,
      p286CoordinateEquiv.apply_symm_apply]
    rcases magnetic with first | second | third <;>
      subst pair <;>
      simp [completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate,
        p286ElectricProjection, p286MagneticProjection]
  · simp

/-- The actual holonomic time row agrees with the generated magnetic write
profile. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_temporalDirectionalDerivative_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current))
        (canonicalCauchySlicePoint time space))
    (profileIntervalIntegrable :
      IntervalIntegrable
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        MeasureTheory.volume 0 time)
    (profileMeasurableAt :
      StronglyMeasurableAtFilter
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        (nhds time) MeasureTheory.volume)
    (profileContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint candidateTime space) pair)
        time) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current)
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair =
        completeJointP286LiveElectricActionTemporalWriteProfile
          source current (canonicalCauchySlicePoint time space) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current)
  change
    (fieldDirectionalDerivative finalCoordinate
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair = _
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
    finalCoordinate
    (canonicalCauchySlicePoint time space)
    canonicalLorentzianTimeDirection pair finalCoordinateDifferentiableAt]
  have actualDerivative :=
    field_timeLine_hasDerivAt
      (fun point => finalCoordinate point pair) space time
      (differentiableAt_pi.mp finalCoordinateDifferentiableAt pair)
  have generatedDerivative :=
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_timeLine_hasDerivAt_of_intervalIntegrable
      source current space time pair magnetic profileIntervalIntegrable
      profileMeasurableAt profileContinuousAt
  exact actualDerivative.unique generatedDerivative

/-- Spatial derivatives of the live electric carrier are preserved because
the generated temporal profile has literal zero electric support. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_electricDirectionalDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (pair : Fin 6)
    (electric : pair = 0 ∨ pair = 1 ∨ pair = 2)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current))
        point)
    (baseCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            source current))
        point) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current) point direction) pair =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        point direction) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current)
  let baseCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286LiveElectricZeroSliceMagneticBase source current)
  change
    (fieldDirectionalDerivative finalCoordinate point direction) pair =
      (fieldDirectionalDerivative baseCoordinate point direction) pair
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt finalCoordinate
    point direction pair finalCoordinateDifferentiableAt]
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt baseCoordinate
    point direction pair baseCoordinateDifferentiableAt]
  have componentEquality :
      (fun candidate => finalCoordinate candidate pair) =
        fun candidate => baseCoordinate candidate pair := by
    funext candidate
    rcases electric with first | second | third
    · subst pair
      exact
        sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroOne
          source current candidate
    · subst pair
      exact
        sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroTwo
          source current candidate
    · subst pair
      exact
        sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate_zeroThree
          source current candidate
  rw [componentEquality]

/-- Each magnetic coordinate of the Cauchy base is constant on canonical
time lines. -/
theorem
    completeJointP286LiveElectricZeroSliceMagneticBase_temporalDirectionalDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (pair : Fin 6)
    (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5)
    (baseCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            source current))
        (canonicalCauchySlicePoint time space)) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (completeJointP286LiveElectricZeroSliceMagneticBase source current)
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair =
      0 := by
  let baseCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286LiveElectricZeroSliceMagneticBase source current)
  change
    (fieldDirectionalDerivative baseCoordinate
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection) pair = 0
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt baseCoordinate
    (canonicalCauchySlicePoint time space) canonicalLorentzianTimeDirection
    pair baseCoordinateDifferentiableAt]
  have actualDerivative :=
    field_timeLine_hasDerivAt
      (fun point => baseCoordinate point pair) space time
      (differentiableAt_pi.mp baseCoordinateDifferentiableAt pair)
  have constantDerivative :
      NormedHasDerivAt
        (fun _ : ℝ =>
          completeJointP286ZeroSliceAnchor source current space pair)
        0 time :=
    hasDerivAt_const time _
  have lineEquality :
      (fun candidateTime =>
        baseCoordinate
          (canonicalCauchySlicePoint candidateTime space) pair) =
        fun _ : ℝ =>
          completeJointP286ZeroSliceAnchor source current space pair := by
    funext candidateTime
    simpa [baseCoordinate] using
      completeJointP286LiveElectricZeroSliceMagneticBase_magnetic
        source current (canonicalCauchySlicePoint candidateTime space)
        pair magnetic
  rw [lineEquality] at actualDerivative
  exact actualDerivative.unique constantDerivative

/-- First producer-soundness gate for the complete P286 Cauchy write.

Every exterior component containing the canonical time direction equals the
same occurrence-native action profile that generated the write.  Coordinate
`123` remains the spatial constitutive compatibility of this one actual. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_exteriorDerivative_temporal
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (triple : Fin 4)
    (temporal : triple ≠ 3)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current))
        (canonicalCauchySlicePoint time space))
    (baseCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            source current))
        (canonicalCauchySlicePoint time space))
    (profileIntervalIntegrable :
      ∀ pair : Fin 6,
        IntervalIntegrable
          (fun candidateTime =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          MeasureTheory.volume 0 time)
    (profileMeasurableAt :
      ∀ pair : Fin 6,
        StronglyMeasurableAtFilter
          (fun candidateTime =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          (nhds time) MeasureTheory.volume)
    (profileContinuousAt :
      ∀ pair : Fin 6,
        ContinuousAt
          (fun candidateTime =>
            completeJointP286LiveElectricActionTemporalWriteProfile
              source current
              (canonicalCauchySlicePoint candidateTime space) pair)
          time) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint time space) triple =
      completeJointP286RequiredExteriorProfile source current
        (canonicalCauchySlicePoint time space) triple := by
  have temporalDerivative
      (pair : Fin 6)
      (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :=
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_temporalDirectionalDerivative_apply
      source current space time pair magnetic finalCoordinateDifferentiableAt
      (profileIntervalIntegrable pair) (profileMeasurableAt pair)
      (profileContinuousAt pair)
  have temporalDerivativeZero
      (pair : Fin 6)
      (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint time space) 0) pair =
          completeJointP286LiveElectricActionTemporalWriteProfile
            source current
            (canonicalCauchySlicePoint time space) pair := by
    simpa [canonicalLorentzianTimeDirection] using
      temporalDerivative pair magnetic
  have electricDerivative
      (direction : LorentzianIndex)
      (pair : Fin 6)
      (electric : pair = 0 ∨ pair = 1 ∨ pair = 2) :=
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_electricDirectionalDerivative
      source current (canonicalCauchySlicePoint time space) direction pair
      electric finalCoordinateDifferentiableAt
      baseCoordinateDifferentiableAt
  have baseTemporalDerivative
      (pair : Fin 6)
      (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :=
    completeJointP286LiveElectricZeroSliceMagneticBase_temporalDirectionalDerivative
      source current space time pair magnetic
      baseCoordinateDifferentiableAt
  have baseTemporalDerivativeZero
      (pair : Fin 6)
      (magnetic : pair = 3 ∨ pair = 4 ∨ pair = 5) :
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint time space) 0) pair =
          0 := by
    simpa [canonicalLorentzianTimeDirection] using
      baseTemporalDerivative pair magnetic
  fin_cases triple
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 5 (Or.inr (Or.inr rfl))]
    rw [electricDerivative 1 1 (Or.inr (Or.inl rfl))]
    rw [electricDerivative 2 0 (Or.inl rfl)]
    rw [completeJointP286LiveElectricActionTemporalWriteProfile_oneTwo]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      baseTemporalDerivativeZero]
    abel
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 4 (Or.inr (Or.inl rfl))]
    rw [electricDerivative 1 2 (Or.inr (Or.inr rfl))]
    rw [electricDerivative 3 0 (Or.inl rfl)]
    rw [completeJointP286LiveElectricActionTemporalWriteProfile_threeOne]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      baseTemporalDerivativeZero]
    abel
  · simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
    rw [temporalDerivativeZero 3 (Or.inl rfl)]
    rw [electricDerivative 2 2 (Or.inr (Or.inr rfl))]
    rw [electricDerivative 3 1 (Or.inr (Or.inl rfl))]
    rw [completeJointP286LiveElectricActionTemporalWriteProfile_twoThree]
    simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      baseTemporalDerivativeZero]
    abel
  · exact (temporal rfl).elim

/-- The action primitive vanishes on the entire zero slice, so the final
producer and its live-electric Cauchy base have the same restriction. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) := by
  funext pair
  simp [sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator,
    completeJointP286LiveElectricZeroSliceMagneticBase,
    holonomicP286GaugeAuxiliaryCoordinate,
    completeJointP286LiveElectricActionTemporalWritePrimitive]

/-- Hence the final producer preserves the spatial first jet of the same
Cauchy base at time zero. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_spatialDirectionalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (pair : Fin 6)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current))
        (canonicalCauchySlicePoint 0 space))
    (baseCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            source current))
        (canonicalCauchySlicePoint 0 space)) :
    (p286GaugeAuxiliaryDirectionalDerivative
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current)
      (canonicalCauchySlicePoint 0 space) direction.succ) pair =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) direction.succ) pair := by
  let finalCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source current)
  let baseCoordinate : BasePoint → P286GaugeTwoForm :=
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointP286LiveElectricZeroSliceMagneticBase source current)
  change
    (fieldDirectionalDerivative finalCoordinate
      (canonicalCauchySlicePoint 0 space) direction.succ) pair =
      (fieldDirectionalDerivative baseCoordinate
        (canonicalCauchySlicePoint 0 space) direction.succ) pair
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local finalCoordinate 0 space
      direction finalCoordinateDifferentiableAt,
    ← fderiv_canonicalCauchySlicePoint_spatial_local baseCoordinate 0 space
      direction baseCoordinateDifferentiableAt]
  have sliceEquality :
      finalCoordinate ∘ canonicalCauchySlicePoint 0 =
        baseCoordinate ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_zeroSlice
        source current candidateSpace
  rw [sliceEquality]

/-- The purely spatial exterior coordinate is therefore inherited from the
same live-electric Cauchy base. -/
theorem
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_exteriorDerivative_spatial_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (finalCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
            source current))
        (canonicalCauchySlicePoint 0 space))
    (baseCoordinateDifferentiableAt :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286LiveElectricZeroSliceMagneticBase
            source current))
        (canonicalCauchySlicePoint 0 space)) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) 3 := by
  simp [holonomicP286GaugeAuxiliaryExteriorDerivative,
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    threeFormFirst, threeFormSecond, threeFormThird,
    orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
    orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six]
  have first :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 1) 3 =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) 1) 3 := by
    simpa using
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_spatialDirectionalDerivative_zeroSlice
        source current space 0 3 finalCoordinateDifferentiableAt
        baseCoordinateDifferentiableAt)
  have second :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 2) 4 =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) 2) 4 := by
    simpa using
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_spatialDirectionalDerivative_zeroSlice
        source current space 1 4 finalCoordinateDifferentiableAt
        baseCoordinateDifferentiableAt)
  have third :
      (p286GaugeAuxiliaryDirectionalDerivative
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source current)
        (canonicalCauchySlicePoint 0 space) 3) 5 =
      (p286GaugeAuxiliaryDirectionalDerivative
        (completeJointP286LiveElectricZeroSliceMagneticBase source current)
        (canonicalCauchySlicePoint 0 space) 3) 5 := by
    simpa using
      (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_spatialDirectionalDerivative_zeroSlice
        source current space 2 5 finalCoordinateDifferentiableAt
        baseCoordinateDifferentiableAt)
  rw [first, second, third]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
