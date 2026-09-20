import H0mework.Physics.SynchronizedJoint.FixedFiveLegSuccessorP286Readback
import H0mework.Physics.ActionForcing.FixedOccurrenceP286ActionForcingBridge
import H0mework.Physics.GaugeAction.P286SpatialVolumeTemporalActionDuality
import H0mework.Physics.Cauchy.ScalarActionTemporalMomentumCarryCauchyDevelopmentOperator

/-!
# Lorentz-path action-selected joint successor

The exact fixed P506/L0 Lorentz-path current selects its radial P286 charge
from the canonical mother-action occurrence profile.  The resulting
coefficient-free radial connection is followed by the live constitutive leg,
the scalar-momentum carry, the coupled scalar/primal/adjoint temporal producer,
and the existing five-leg full-occurrence compiler.

Every constructor consumes only the fixed source and the preceding generated
current.  The current P286 Euler read is used solely to prove that the
action-selected charge agrees with the established mother-action charge; no
residual coordinate, support, target field, zero-fiber receipt, or branch
enters the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286ConnectionScalarReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ActionForcingBridge
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286GaugeConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance spliceP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance spliceP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance spliceP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private abbrev Recentered (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Current contact

private abbrev LocalTemporal (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (Recentered contact)

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem current_gaugeAuxiliary_eq_constitutive :
    Current.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Current := by
  funext point
  have residualZero := final_p286AuxiliaryResidual_allPoint_zero point
  have equation :=
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Current point)).1 residualZero
  have nondegenerate : Matrix.det (Current.coframe point) ≠ 0 :=
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_nondegenerate
      point
  have eliminated :=
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Current point) nondegenerate).1 equation
  change
    Current.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Current.coframe point) (holonomicGaugeCurvature Current point)
  exact eliminated

private theorem constitutiveReadout_fullyRecenter
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    formNativeP286GaugeConstitutiveReadout Source
        (fullyRecenterHolonomicConfiguration current contact) =
      fullyRecenterHolonomicConfiguration
        (formNativeP286GaugeConstitutiveReadout Source current) contact := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point pair
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (current.coframe
            (canonicalSpacetimeContactTranslation contact point))
          (holonomicGaugeCurvature
            (fullyRecenterHolonomicConfiguration current contact) point) pair =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (current.coframe
            (canonicalSpacetimeContactTranslation contact point))
          (holonomicGaugeCurvature current
            (canonicalSpacetimeContactTranslation contact point)) pair
  have pointFieldEq :=
    fullyRecenterHolonomicConfiguration_pointField_unconditional
      current contact point
  have curvatureEq :
      holonomicGaugeCurvature
          (fullyRecenterHolonomicConfiguration current contact) point =
        holonomicGaugeCurvature current
          (canonicalSpacetimeContactTranslation contact point) :=
    congrArg (fun field : StageNineContinuumPointField => field.gaugeCurvature)
      pointFieldEq
  rw [curvatureEq]

private theorem current_eq_constitutiveReadout :
    formNativeP286GaugeConstitutiveReadout Source Current = Current := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  exact current_gaugeAuxiliary_eq_constitutive.symm

private theorem recentered_eq_constitutiveReadout
    (contact : BasePoint) :
    formNativeP286GaugeConstitutiveReadout Source (Recentered contact) =
      Recentered contact := by
  rw [constitutiveReadout_fullyRecenter, current_eq_constitutiveReadout]

private theorem localTemporal_scalarAcceleration_contDiffAt
    (contact : BasePoint) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile Source (Recentered contact)) 0 := by
  apply (completeJointScalarAccelerationProfile_contDiffAt_of_local
    Source (Recentered contact) 0)
  · rw [fullyRecenterHolonomicConfiguration_coframe_origin,
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
    norm_num
  · change ContDiffAt ℝ ∞
      (Current.coframe ∘ canonicalSpacetimeContactTranslation contact) 0
    rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
    exact contDiff_const.contDiffAt
  · change ContDiffAt ℝ ∞
      (Current.scalar ∘ canonicalSpacetimeContactTranslation contact) 0
    change ContDiffAt ℝ ∞
      (Raw.scalar ∘ canonicalSpacetimeContactTranslation contact) 0
    exact
      (fixedP506L0CompleteJointActionSpacetimeSection_scalar_contDiff.comp
        (by
          unfold canonicalSpacetimeContactTranslation
          fun_prop)).contDiffAt
  · change ContDiffAt ℝ ∞
      ((fun point => matterCoordinateEquiv (Raw.matter point)) ∘
        canonicalSpacetimeContactTranslation contact) 0
    exact
      (fixedP506L0CompleteJointActionSpacetimeSection_matter_contDiff.comp
        (by
          unfold canonicalSpacetimeContactTranslation
          fun_prop)).contDiffAt
  · change ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates Raw ∘
        canonicalSpacetimeContactTranslation contact) 0
    exact
      (fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatterCoordinates_contDiff.comp
        (by
          unfold canonicalSpacetimeContactTranslation
          fun_prop)).contDiffAt
  · intro direction
    change ContDiffAt ℝ ∞
      ((fun point =>
          p286CoordinateEquiv
            (Current.gaugeConnection point direction)) ∘
        canonicalSpacetimeContactTranslation contact) 0
    rw [final_gaugeConnection_eq_input]
    exact
      (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
          direction).comp
        (by
          unfold canonicalSpacetimeContactTranslation
          fun_prop) |>.contDiffAt

private theorem localTemporal_scalarFirstJet_eq_recentered
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative (LocalTemporal contact) 0 =
      holonomicScalarCovariantDerivative (Recentered contact) 0 := by
  have secondPrimitive :
      HasFDerivAt
        (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source (Recentered contact)))
        (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 :=
    canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
      (completeJointScalarAccelerationProfile Source (Recentered contact))
      ((localTemporal_scalarAcceleration_contDiffAt contact).of_le
        (by norm_num))
  have recenteredScalar :
      DifferentiableAt ℝ (Recentered contact).scalar 0 := by
    change DifferentiableAt ℝ
      (Raw.scalar ∘ canonicalSpacetimeContactTranslation contact) 0
    exact
      ((fixedP506L0CompleteJointActionSpacetimeSection_scalar_contDiff.comp
        (by
          unfold canonicalSpacetimeContactTranslation
          fun_prop)).differentiable (by simp)).differentiableAt
  have localScalar :
      DifferentiableAt ℝ (LocalTemporal contact).scalar 0 := by
    change DifferentiableAt ℝ
      (fun point =>
        (Recentered contact).scalar point +
          canonicalTimeSecondPrimitive
            (completeJointScalarAccelerationProfile Source
              (Recentered contact)) point) 0
    exact recenteredScalar.add secondPrimitive.differentiableAt
  funext direction
  unfold holonomicScalarCovariantDerivative
  have derivativeEq :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
      Source (Recentered contact) 0
      (by
        simpa only [canonicalCauchySlicePoint_zero_zero_local] using
          recenteredScalar)
      (by
        simpa only [canonicalCauchySlicePoint_zero_zero_local, LocalTemporal,
          completeJointGlobalTemporalCurrent] using localScalar)
      direction
  have derivativeEq' :
      fieldDirectionalDerivative (LocalTemporal contact).scalar 0 direction =
        fieldDirectionalDerivative (Recentered contact).scalar 0 direction := by
    simpa only [canonicalCauchySlicePoint_zero_zero_local, LocalTemporal,
      completeJointGlobalTemporalCurrent] using derivativeEq
  rw [derivativeEq']
  simp [LocalTemporal, completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    canonicalTimeSecondPrimitive]

private theorem localTemporal_coframe_eq_recentered
    (contact : BasePoint) :
    (LocalTemporal contact).coframe = (Recentered contact).coframe :=
  rfl

private theorem localTemporal_gaugeConnection_eq_recentered
    (contact : BasePoint) :
    (LocalTemporal contact).gaugeConnection =
      (Recentered contact).gaugeConnection :=
  rfl

private theorem localTemporal_scalar_origin_eq_recentered
    (contact : BasePoint) :
    (LocalTemporal contact).scalar 0 = (Recentered contact).scalar 0 := by
  unfold LocalTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  simp [canonicalTimeSecondPrimitive]

private theorem localTemporal_matter_origin_eq_recentered
    (contact : BasePoint) :
    (LocalTemporal contact).matter 0 = (Recentered contact).matter 0 := by
  unfold LocalTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  simp [canonicalTimePrimitive]

private theorem localTemporal_conjugateMatter_origin_eq_recentered
    (contact : BasePoint) :
    (LocalTemporal contact).conjugateMatter 0 =
      (Recentered contact).conjugateMatter 0 := by
  unfold LocalTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  simp [canonicalTimePrimitive]

private theorem recentered_p286Euler_origin_eq_current
    (contact : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (Recentered contact) 0 =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current contact := by
  have residualEq :=
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      Source (Recentered contact) Current 0 contact
      (generatedActionJet_fullyRecenter_origin_unconditional Source Current
        contact)
  exact congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection) residualEq

private theorem localTemporal_originActionForcing_eq_currentEuler
    (contact : BasePoint) :
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (LocalTemporal contact) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current contact) := by
  calc
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (LocalTemporal contact) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (Recentered contact) := by
      apply
        diracDualFormNativeP286CanonicalOriginActionForcing_eq_of_actionData_eq
      · exact localTemporal_coframe_eq_recentered contact
      · exact localTemporal_gaugeConnection_eq_recentered contact
      · exact localTemporal_scalar_origin_eq_recentered contact
      · exact localTemporal_scalarFirstJet_eq_recentered contact
      · exact localTemporal_matter_origin_eq_recentered contact
      · exact localTemporal_conjugateMatter_origin_eq_recentered contact
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0
          (Recentered contact) 0) := by
      unfold diracDualFormNativeP286CanonicalOriginActionForcing
        diracDualFormNativeP286CanonicalOriginActionDual
        diracDualFormNativeP286CanonicalJointCandidate
      rw [diracDualFormNativeP286CanonicalConnectionCandidate_zero,
        recentered_eq_constitutiveReadout]
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current
          contact) := by
      rw [recentered_p286Euler_origin_eq_current]

/-! ## Current-owned radial principal selection -/

/-- The complete occurrence response is the explicit W13 rotation of the
same-current Euler three-form.  The result reads an action-selected write;
the Euler form does not enter any constructor. -/
theorem current_occurrenceWriteProfile_eq_eulerNormalForm
    (contact : BasePoint) :
    completeJointP286CanonicalOccurrenceWriteProfile Source Current contact =
      p286GaugeThreeFormOccurrenceOneFormNormalForm
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current
          contact) := by
  unfold completeJointP286CanonicalOccurrenceWriteProfile
    diracDualFormNativeP286CanonicalGeneratedWrite
  rw [localTemporal_originActionForcing_eq_currentEuler]
  exact p286PairingInverse_wedgeDual_allComponents _

/-- On the canonical zero slice, the temporal component selected by the
current occurrence is exactly the radial mother-action charge density. -/
theorem current_occurrenceWriteProfile_zeroSlice_temporal
    (space : StageNineSpatialPoint) :
    completeJointP286CanonicalOccurrenceWriteProfile Source Current
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
        fixedP506L0U6OccurrenceP286MotherActionCharge := by
  let point := canonicalCauchySlicePoint 0 space
  calc
    completeJointP286CanonicalOccurrenceWriteProfile Source Current point
        canonicalLorentzianTimeDirection =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current point 3 := by
        have component := congrFun
          (current_occurrenceWriteProfile_eq_eulerNormalForm point)
          canonicalLorentzianTimeDirection
        simpa [p286GaugeThreeFormOccurrenceOneFormNormalForm,
          canonicalLorentzianTimeDirection, oneWedgeThreeSign,
          missingTripleOfOneForm] using component
    _ = p286SpatialRadiusSquared point •
        fixedP506L0U6OccurrenceP286MotherActionCharge := by
      exact final_p286GaugeConnectionResidual_zeroSlice_spatialVolume space

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

private def PointE0 : BasePoint :=
  canonicalCauchySlicePoint 0 SpatialE0

/-- Canonical source/current-only radial charge reader.  The unit-spatial
occurrence and temporal direction are fixed by the Stage-9 chart. -/
def completeJointActionSelectedRadialCharge
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : P286CoordinateCarrier :=
  completeJointP286CanonicalOccurrenceWriteProfile source current PointE0
    canonicalLorentzianTimeDirection

/-- The radial charge is selected from the current action occurrence at the
fixed unit-spatial point; it is not supplied as a coefficient. -/
def fixedP506L0LorentzPathActionSelectedRadialCharge :
    P286CoordinateCarrier :=
  completeJointActionSelectedRadialCharge Source Current

theorem fixedP506L0LorentzPathActionSelectedRadialCharge_eq_motherActionCharge :
    fixedP506L0LorentzPathActionSelectedRadialCharge =
      fixedP506L0U6OccurrenceP286MotherActionCharge := by
  have selected := current_occurrenceWriteProfile_zeroSlice_temporal SpatialE0
  have radius :
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 SpatialE0) = 1 := by
    simp [SpatialE0, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, p286BaseCoordinate_apply,
      Fin.sum_univ_three]
  unfold fixedP506L0LorentzPathActionSelectedRadialCharge
    completeJointActionSelectedRadialCharge PointE0
  rw [selected, radius, one_smul]

/-! ## One source/current-only lifted common writer -/

/-- Coefficient-free radial principal generated from the canonical occurrence
charge of the supplied source/current pair. -/
def completeJointActionSelectedRadialConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → P286GaugeOneForm :=
  p286RadialQuarticTemporalConnection
    (completeJointActionSelectedRadialCharge source current)

/-- Install the action-selected radial connection on the same current. -/
def completeJointActionSelectedRadialConnectionActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate current
    (completeJointActionSelectedRadialConnection source current) 1

/-- Recompute the live constitutive auxiliary after the radial write. -/
def completeJointActionSelectedRadialConstitutiveActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent source
    (completeJointActionSelectedRadialConnectionActual source current)

/-- Carry the same-current scalar action momentum through the new connection. -/
def completeJointActionSelectedScalarMomentumCarryActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  scalarActionTemporalMomentumCarryCauchyDevelopmentOperator source current
    (completeJointActionSelectedRadialConstitutiveActual source current)

/-- Run the scalar, primal, and adjoint temporal action producer on the same
radial-plus-momentum current. -/
def completeJointActionSelectedCoupledTemporalActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    source (completeJointActionSelectedScalarMomentumCarryActual source current)

/-- Generic source/current-only composite write used by the generated-time
query below.  Its inventory and order are fixed before the output is read. -/
def sourceActionGeneratedCompleteJointActionSelectedSuccessorOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
    source (completeJointActionSelectedCoupledTemporalActual source current)

/-- One common whole-spacetime actual: action-selected radial principal,
constitutive response, scalar momentum carry, coupled temporal producer, then
the existing five-leg full-occurrence compiler. -/
def fixedP506L0LorentzPathActionSelectedJointSuccessor :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedCompleteJointActionSelectedSuccessorOperator
    Source Current

/-- Source-indexed full residual read and the independently fixed composite
action write. -/
def fixedP506L0LorentzPathActionSelectedJointQuery :
    ReflexiveQuery StageNineHolonomicConfiguration
      (BasePoint → DiracDualFormNativePointwiseJointResidualCarrier) where
  read := diracDualFormNativeJointResidualSection Source
  write := sourceActionGeneratedCompleteJointActionSelectedSuccessorOperator
    Source

/-- Canonical two-section development of the concrete source/current-only
joint writer. -/
def fixedP506L0LorentzPathActionSelectedGeneratedTimeStep :=
  reflexiveQueryGeneratedTimeStep
    fixedP506L0LorentzPathActionSelectedJointQuery Current

@[simp] theorem
    fixedP506L0LorentzPathActionSelectedGeneratedTimeStep_now_eq_current :
    fixedP506L0LorentzPathActionSelectedGeneratedTimeStep.field.stateAt
        fixedP506L0LorentzPathActionSelectedGeneratedTimeStep.now =
      Current :=
  rfl

@[simp] theorem
    fixedP506L0LorentzPathActionSelectedGeneratedTimeStep_next_eq_successor :
    fixedP506L0LorentzPathActionSelectedGeneratedTimeStep.field.stateAt
        fixedP506L0LorentzPathActionSelectedGeneratedTimeStep.next =
      fixedP506L0LorentzPathActionSelectedJointSuccessor :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
