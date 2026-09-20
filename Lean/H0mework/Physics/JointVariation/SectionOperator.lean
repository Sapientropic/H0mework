import H0mework.Physics.JointVariation.ResponseOperator
import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.ConstitutiveAction.SpatialSectionGaugeClosure
import H0mework.Physics.ConstitutiveAction.SpatialSectionOperator
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier
import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.Geometry.IIPlusRestriction
import H0mework.Physics.Lorentz.LorentzGeometricKinematics

/-!
# Spacetime-section lift of the complete joint action write

The complete joint contact operator is already generated from `(source,
current)`.  This module lifts that same operator to one four-dimensional
`StageNineHolonomicConfiguration`: translate the one current to every
canonical spatial contact, run the complete joint action there, and read the
result along that contact's physical-time axis.

The matching contacts below are readouts of this one global write.  They are
not a supplied family of candidate worlds.  The assembly-seam carrier is
computed only after both action jets exist and exhausts every derived jet
coordinate that diagonalization can change.  It is not accepted by the
global constructor and does not define a correction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineIIPlusRestriction
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field
      (canonicalSpatialContactTranslation space point)) :
    fieldDirectionalDerivative
        (field ∘ canonicalSpatialContactTranslation space) point direction =
      fieldDirectionalDerivative field
        (canonicalSpatialContactTranslation space point) direction := by
  have translation :
      HasFDerivAt (canonicalSpatialContactTranslation space)
        (ContinuousLinearMap.id ℝ BasePoint) point := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have composed := differentiable.hasFDerivAt.comp point translation
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  rfl

/-! ## One source/current-only global write -/

/-- The complete joint action contact generated at one canonical spatial
contact of the supplied current.  The current-native Cartan/reaction restart
is recomputed at that same contact before the four complete-joint legs. -/
def completeJointActionSpatialContact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointActionResponseOperator source
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      (spatiallyRecenterHolonomicConfiguration current space))

/-- One branch-free four-dimensional write assembled from the complete joint
action at every canonical spatial contact.  Its inputs are exactly one source
and one current; no residual, seam, target field, branch, or zero receipt is
accepted. -/
def sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal
    (completeJointActionSpatialContact source current)

/-- Matching action-generated contact used to read the global section at one
spacetime occurrence. -/
def completeJointActionMatchingContact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointActionSpatialContact source current
    (canonicalSpatialProjection point)

/-- The local occurrence of the matching contact carrying the same physical
time coordinate as the global occurrence. -/
def completeJointActionMatchingContactPoint
    (point : BasePoint) : BasePoint :=
  canonicalCauchySlicePoint (canonicalTimeProjection point) 0

macro "complete_joint_section_field_at" : tactic =>
  `(tactic|
    rfl)

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).coframe point =
      (completeJointActionMatchingContact source current point).coframe
        (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gravityConnection point =
      (completeJointActionMatchingContact source current point
        ).gravityConnection (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gravityAuxiliary point =
      (completeJointActionMatchingContact source current point
        ).gravityAuxiliary (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_multiplier_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gravitySimplicityMultiplier point =
      (completeJointActionMatchingContact source current point
        ).gravitySimplicityMultiplier
          (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gaugeConnection point =
      (completeJointActionMatchingContact source current point
        ).gaugeConnection (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeAuxiliary_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gaugeAuxiliary point =
      (completeJointActionMatchingContact source current point
        ).gaugeAuxiliary (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_scalar_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).scalar point =
      (completeJointActionMatchingContact source current point).scalar
        (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_matter_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).matter point =
      (completeJointActionMatchingContact source current point).matter
        (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_conjugateMatter_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).conjugateMatter point =
      (completeJointActionMatchingContact source current point
        ).conjugateMatter (completeJointActionMatchingContactPoint point) := by
  complete_joint_section_field_at

/-- The spacetime-section write preserves the supplied coframe globally.
Every contact leg preserves the recentered coframe, and the diagonal reads it
back at the matching global occurrence. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).coframe = current.coframe := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe_at]
  simp [completeJointActionMatchingContact,
    completeJointActionMatchingContactPoint, completeJointActionSpatialContact,
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_timeAxis]

/-- The single spacetime-section write satisfies the action-generated
simplicity equation globally.  Each point reads the matching complete-joint
contact, whose auxiliary field was generated as the computed `II+` of that
same contact coframe. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
        source current) := by
  intro point
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary_at,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe_at]
  unfold completeJointActionMatchingContact completeJointActionSpatialContact
  exact
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_simplicity
      source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
        (spatiallyRecenterHolonomicConfiguration current
          (canonicalSpatialProjection point)))
      (completeJointActionMatchingContactPoint point)

/-- The global auxiliary field is exactly the action-owned computed `II+` of
the input coframe.  This is a field equality, not only a pointwise residual
readout. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gravityAuxiliary =
      fun point => physicalIIPlusBivector (current.coframe point) := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_simplicity
      source current point,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe]

/-- A matching contact carries the same computed-`II+` field pulled back by
its canonical spatial translation. -/
theorem completeJointActionMatchingContact_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointActionMatchingContact source current point
      ).gravityAuxiliary =
      (fun candidate => physicalIIPlusBivector (current.coframe candidate)) ∘
        canonicalSpatialContactTranslation
          (canonicalSpatialProjection point) := by
  funext localPoint
  have simplicity :
      FormNativeGravitySimplicityEquation
        (completeJointActionMatchingContact source current point) := by
    unfold completeJointActionMatchingContact completeJointActionSpatialContact
    exact
      sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_simplicity
        source _
  rw [simplicity localPoint]
  simp [completeJointActionMatchingContact, completeJointActionSpatialContact,
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    spatiallyRecenterHolonomicConfiguration]

/-- The auxiliary first jet of the one global write agrees with the matching
contact first jet at the same spacetime occurrence.  Smoothness transports
only the explicitly generated computed-`II+` field through the canonical
translation. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliaryDirectionalDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    gravityAuxiliaryDirectionalDerivative
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          source current) point =
      gravityAuxiliaryDirectionalDerivative
        (completeJointActionMatchingContact source current point)
        (completeJointActionMatchingContactPoint point) := by
  have computedIIPlusSmooth :
      ContDiff ℝ ∞
        (fun candidate =>
          physicalIIPlusBivector (current.coframe candidate)) :=
    StageNineIIPlusRestriction.physicalIIPlusBivector_contDiff.comp
      (holonomicCoframe_contDiff current smooth)
  have computedIIPlusDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          physicalIIPlusBivector (current.coframe candidate))
        (canonicalSpatialContactTranslation
          (canonicalSpatialProjection point)
          (completeJointActionMatchingContactPoint point)) :=
    (computedIIPlusSmooth.differentiable (by simp)).differentiableAt
  funext direction
  unfold gravityAuxiliaryDirectionalDerivative
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary,
    completeJointActionMatchingContact_gravityAuxiliary,
    fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      (fun candidate =>
        physicalIIPlusBivector (current.coframe candidate))
      (canonicalSpatialProjection point)
      (completeJointActionMatchingContactPoint point) direction
      computedIIPlusDifferentiable,
    completeJointActionMatchingContactPoint,
    canonicalSpatialContactTranslation_timeAxis,
    canonicalCauchySlicePoint_projections]

/-- The complete gravity-auxiliary exterior covariant derivative is therefore
faithfully assembled at every spacetime occurrence.  Both the auxiliary jet
and the connection value come from the same source/current-only global write. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliaryExteriorCovariantDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          source current) point =
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        (completeJointActionMatchingContact source current point)
        (completeJointActionMatchingContactPoint point) := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at]
  apply congrArg
    (pointwisePhysicalBivectorExteriorCovariantDerivative
      ((completeJointActionMatchingContact source current point
        ).gravityConnection (completeJointActionMatchingContactPoint point)))
  congr 1
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliaryDirectionalDerivative
      source current smooth point

/-- The spacetime-section write also preserves the complete P286 connection
field globally.  Consequently any later gauge-curvature comparison is an
action-jet readout, not a new gauge write. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current).gaugeConnection = current.gaugeConnection := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at]
  simp [completeJointActionMatchingContact,
    completeJointActionMatchingContactPoint, completeJointActionSpatialContact,
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_timeAxis]

/-- The one global section has exactly the input P286 curvature.  This is a
readout of the action-owned full-connection preservation theorem. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          source current) point =
      holonomicGaugeCurvature current point :=
  holonomicGaugeCurvature_eq_of_connection_eq
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      source current)
    current
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
      source current)
    point

/-- The matching contact reads the same P286 curvature as the input current at
the corresponding global occurrence.  Smoothness is used only to transport
the literal connection first jet through canonical spatial translation. -/
theorem completeJointActionMatchingContact_gaugeCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (completeJointActionMatchingContact source current point)
        (completeJointActionMatchingContactPoint point) =
      holonomicGaugeCurvature current point := by
  have contactConnection :
      (completeJointActionMatchingContact source current point
        ).gaugeConnection =
        (spatiallyRecenterHolonomicConfiguration current
          (canonicalSpatialProjection point)).gaugeConnection := by
    simp [completeJointActionMatchingContact, completeJointActionSpatialContact]
  calc
    holonomicGaugeCurvature
          (completeJointActionMatchingContact source current point)
          (completeJointActionMatchingContactPoint point) =
        holonomicGaugeCurvature
          (spatiallyRecenterHolonomicConfiguration current
            (canonicalSpatialProjection point))
          (completeJointActionMatchingContactPoint point) :=
      holonomicGaugeCurvature_eq_of_connection_eq
        (completeJointActionMatchingContact source current point)
        (spatiallyRecenterHolonomicConfiguration current
          (canonicalSpatialProjection point))
        contactConnection
        (completeJointActionMatchingContactPoint point)
    _ = holonomicGaugeCurvature current
          (canonicalSpatialContactTranslation
            (canonicalSpatialProjection point)
            (completeJointActionMatchingContactPoint point)) :=
      holonomicGaugeCurvature_spatiallyRecenter current smooth
        (canonicalSpatialProjection point)
        (completeJointActionMatchingContactPoint point)
    _ = holonomicGaugeCurvature current point := by
      rw [completeJointActionMatchingContactPoint,
        canonicalSpatialContactTranslation_timeAxis,
        canonicalCauchySlicePoint_projections]

/-! ## Exhaustive action-jet assembly seam -/

/-- Every derived action-jet coordinate that can change when the generated
contact family is read through the single global diagonal section.

Primitive point-field values and the two connection values are deliberately
absent: the diagonal constructor preserves them definitionally at the
matching occurrence. -/
@[ext] structure CompleteJointActionJetAssemblySeam where
  gravityCurvature : PhysicalBivector
  gaugeCurvature : Fin 6 → P286LieBlockData
  scalarCovariantDerivative :
    LorentzianIndex → ScalarCoordinateCarrier
  matterCovariantDerivative :
    LorentzianIndex → DiracExteriorMatterCarrier
  gravityAuxiliaryExteriorCovariantDerivative : PhysicalBivectorThreeForm
  p286GaugeAuxiliaryExteriorCovariantDerivative : P286GaugeThreeForm
  scalarDifferentialMomentumDivergence : ScalarCoordinateCarrier → ℝ
  matterDifferentialMomentumDivergence : MatterCoordinateCarrier → ℝ

instance : Zero CompleteJointActionJetAssemblySeam where
  zero :=
    { gravityCurvature := 0
      gaugeCurvature := 0
      scalarCovariantDerivative := 0
      matterCovariantDerivative := 0
      gravityAuxiliaryExteriorCovariantDerivative := 0
      p286GaugeAuxiliaryExteriorCovariantDerivative := 0
      scalarDifferentialMomentumDivergence := 0
      matterDifferentialMomentumDivergence := 0 }

@[simp] theorem completeJointActionJetAssemblySeam_zero_gravityCurvature :
    (0 : CompleteJointActionJetAssemblySeam).gravityCurvature = 0 :=
  rfl

@[simp] theorem completeJointActionJetAssemblySeam_zero_gaugeCurvature :
    (0 : CompleteJointActionJetAssemblySeam).gaugeCurvature = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_scalarCovariantDerivative :
    (0 : CompleteJointActionJetAssemblySeam).scalarCovariantDerivative = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_matterCovariantDerivative :
    (0 : CompleteJointActionJetAssemblySeam).matterCovariantDerivative = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_gravityAuxiliaryDerivative :
    (0 : CompleteJointActionJetAssemblySeam
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_p286GaugeAuxiliaryDerivative :
    (0 : CompleteJointActionJetAssemblySeam
      ).p286GaugeAuxiliaryExteriorCovariantDerivative = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_scalarDivergence :
    (0 : CompleteJointActionJetAssemblySeam
      ).scalarDifferentialMomentumDivergence = 0 :=
  rfl

@[simp] theorem
    completeJointActionJetAssemblySeam_zero_matterDivergence :
    (0 : CompleteJointActionJetAssemblySeam
      ).matterDifferentialMomentumDivergence = 0 :=
  rfl

/-- The assembly seam generated by two already-evaluated action jets.  The
first jet is the global-section read; the second is the matching-contact read.
No seam coordinate is used to produce either jet. -/
def completeJointActionJetAssemblySeam
    (sectionJet contactJet : DiracDualFormNativePointwiseActionJetCarrier) :
    CompleteJointActionJetAssemblySeam :=
  { gravityCurvature :=
      sectionJet.pointField.gravityCurvature -
        contactJet.pointField.gravityCurvature
    gaugeCurvature :=
      sectionJet.pointField.gaugeCurvature -
        contactJet.pointField.gaugeCurvature
    scalarCovariantDerivative :=
      sectionJet.pointField.scalarCovariantDerivative -
        contactJet.pointField.scalarCovariantDerivative
    matterCovariantDerivative :=
      sectionJet.pointField.matterCovariantDerivative -
        contactJet.pointField.matterCovariantDerivative
    gravityAuxiliaryExteriorCovariantDerivative :=
      sectionJet.gravityAuxiliaryExteriorCovariantDerivative -
        contactJet.gravityAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryExteriorCovariantDerivative :=
      sectionJet.p286GaugeAuxiliaryExteriorCovariantDerivative -
        contactJet.p286GaugeAuxiliaryExteriorCovariantDerivative
    scalarDifferentialMomentumDivergence :=
      sectionJet.scalarDifferentialMomentumDivergence -
        contactJet.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      sectionJet.matterDifferentialMomentumDivergence -
        contactJet.matterDifferentialMomentumDivergence }

/-- The gauge-curvature coordinate of the generated whole-section seam is
identically zero.  Unlike the defining reconstruction of the seam, this uses
the native connection write plus faithful curvature transport and therefore
closes a genuine assembly responsibility. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_assemblySeam_gaugeCurvature_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    (completeJointActionJetAssemblySeam
        (generatedDiracDualFormNativePointwiseActionJet source
          (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
            source current) point)
        (generatedDiracDualFormNativePointwiseActionJet source
          (completeJointActionMatchingContact source current point)
          (completeJointActionMatchingContactPoint point))).gaugeCurvature =
      0 := by
  change
    holonomicGaugeCurvature
          (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
            source current) point -
        holonomicGaugeCurvature
          (completeJointActionMatchingContact source current point)
          (completeJointActionMatchingContactPoint point) =
      0
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeCurvature,
    completeJointActionMatchingContact_gaugeCurvature source current smooth]
  exact sub_self _

/-- The gravity-auxiliary derivative coordinate of the generated whole-
section seam is identically zero on the complete spacetime domain. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_assemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    (completeJointActionJetAssemblySeam
        (generatedDiracDualFormNativePointwiseActionJet source
          (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
            source current) point)
        (generatedDiracDualFormNativePointwiseActionJet source
          (completeJointActionMatchingContact source current point)
          (completeJointActionMatchingContactPoint point))
      ).gravityAuxiliaryExteriorCovariantDerivative =
      0 := by
  change
    holonomicGravityAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
            source current) point -
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (completeJointActionMatchingContact source current point)
          (completeJointActionMatchingContactPoint point) =
      0
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliaryExteriorCovariantDerivative
      source current smooth point]
  exact sub_self _

/-- Install an already-generated assembly seam into a matching-contact jet.
This is a diagnostic reconstruction used to state naturality; it is not a
physics write on `StageNineHolonomicConfiguration`. -/
def pointwiseActionJetWithCompleteJointAssemblySeam
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : CompleteJointActionJetAssemblySeam) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { contactJet with
    pointField :=
      { contactJet.pointField with
        gravityCurvature :=
          seam.gravityCurvature + contactJet.pointField.gravityCurvature
        gaugeCurvature :=
          seam.gaugeCurvature + contactJet.pointField.gaugeCurvature
        scalarCovariantDerivative :=
          seam.scalarCovariantDerivative +
            contactJet.pointField.scalarCovariantDerivative
        matterCovariantDerivative :=
          seam.matterCovariantDerivative +
            contactJet.pointField.matterCovariantDerivative }
    gravityAuxiliaryExteriorCovariantDerivative :=
      seam.gravityAuxiliaryExteriorCovariantDerivative +
        contactJet.gravityAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryExteriorCovariantDerivative :=
      seam.p286GaugeAuxiliaryExteriorCovariantDerivative +
        contactJet.p286GaugeAuxiliaryExteriorCovariantDerivative
    scalarDifferentialMomentumDivergence :=
      seam.scalarDifferentialMomentumDivergence +
        contactJet.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      seam.matterDifferentialMomentumDivergence +
        contactJet.matterDifferentialMomentumDivergence }

@[simp] theorem pointwiseActionJetWithCompleteJointAssemblySeam_zero
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier) :
    pointwiseActionJetWithCompleteJointAssemblySeam contactJet 0 =
      contactJet := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext <;>
      simp [pointwiseActionJetWithCompleteJointAssemblySeam]
  all_goals simp [pointwiseActionJetWithCompleteJointAssemblySeam]

/-- Installing a complete assembly seam is faithful: the resulting action
jet is unchanged exactly when every seam coordinate is zero.  Thus a nonzero
seam is an actual pointwise effect, not merely an attached residual label. -/
theorem pointwiseActionJetWithCompleteJointAssemblySeam_eq_contact_iff
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : CompleteJointActionJetAssemblySeam) :
    pointwiseActionJetWithCompleteJointAssemblySeam contactJet seam =
        contactJet ↔
      seam = 0 := by
  constructor
  · intro unchanged
    apply CompleteJointActionJetAssemblySeam.ext
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.pointField.gravityCurvature) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.pointField.gaugeCurvature) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.pointField.scalarCovariantDerivative) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.pointField.matterCovariantDerivative) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg
          (fun jet => jet.gravityAuxiliaryExteriorCovariantDerivative) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg
          (fun jet => jet.p286GaugeAuxiliaryExteriorCovariantDerivative) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.scalarDifferentialMomentumDivergence) unchanged
    · simpa [pointwiseActionJetWithCompleteJointAssemblySeam] using
        congrArg (fun jet => jet.matterDifferentialMomentumDivergence) unchanged
  · rintro rfl
    exact pointwiseActionJetWithCompleteJointAssemblySeam_zero contactJet

/-! ## Whole-section action-jet naturality -/

/-- At every spacetime occurrence, the complete action jet of the one global
write is the matching action-generated contact jet plus exactly the eight
listed derived assembly seams.  Primitive field values and connection values
match literally.

This theorem classifies the whole carrier before any nine-channel residual is
read.  It neither assumes nor concludes that a seam vanishes. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_actionJet_naturality
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    let sectionJet :=
      generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          source current) point
    let contactJet :=
      generatedDiracDualFormNativePointwiseActionJet source
        (completeJointActionMatchingContact source current point)
        (completeJointActionMatchingContactPoint point)
    sectionJet =
      pointwiseActionJetWithCompleteJointAssemblySeam contactJet
        (completeJointActionJetAssemblySeam sectionJet contactJet) := by
  dsimp only
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary_at
          source current point
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_multiplier_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeAuxiliary_at
          source current point
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_scalar_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_matter_at
          source current point
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        completeJointActionJetAssemblySeam]
    · exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_conjugateMatter_at
          source current point
  · exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at
        source current point
  · exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at
        source current point
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      completeJointActionJetAssemblySeam]

/-- Once the internally generated assembly seam is zero, whole-section
action-jet naturality becomes literal equality with the matching contact.
The zero proof is a downstream obligation; it is not an input to the global
write. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_actionJet_eq_contact_of_seam_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (seamZero :
      completeJointActionJetAssemblySeam
          (generatedDiracDualFormNativePointwiseActionJet source
            (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
              source current) point)
          (generatedDiracDualFormNativePointwiseActionJet source
            (completeJointActionMatchingContact source current point)
            (completeJointActionMatchingContactPoint point)) =
        0) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          source current) point =
      generatedDiracDualFormNativePointwiseActionJet source
        (completeJointActionMatchingContact source current point)
        (completeJointActionMatchingContactPoint point) := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSection_actionJet_naturality
      source current point,
    seamZero,
    pointwiseActionJetWithCompleteJointAssemblySeam_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
