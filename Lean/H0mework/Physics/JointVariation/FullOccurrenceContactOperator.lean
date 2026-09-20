import H0mework.Physics.JointVariation.SectionOperator

/-!
# Full-occurrence complete-joint action contact

This module supplies the internal action leg needed by a later jet-faithful
global write.  A spacetime occurrence canonically translates all nine fields
of one current to a common local origin; the existing source/current-only
Cartan restart and complete-joint action are then recomputed on that one
translated current.

The contact is not a world and is not supplied to the global constructor.  It
accepts no residual, seam, support, target field, branch, or equation receipt.
Its action jet at the local origin is the canonical recentered action leg that
a later global integrability operator must realize faithfully.  Identifying
this leg with a direct arbitrary-point action is deliberately left to the
whole-action-jet naturality theorem.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fullOccurrenceP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

/-! ## Canonical four-dimensional contact translation -/

/-- Translate a local coordinate so that its origin is the selected physical
spacetime occurrence.  The occurrence is a read from the global base carrier,
not a branch or a tunable boundary constant. -/
def canonicalSpacetimeContactTranslation
    (contact point : BasePoint) : BasePoint :=
  contact + point

@[simp] theorem canonicalSpacetimeContactTranslation_zero
    (contact : BasePoint) :
    canonicalSpacetimeContactTranslation contact 0 = contact := by
  simp [canonicalSpacetimeContactTranslation]

@[simp] theorem canonicalSpacetimeContactTranslation_zeroContact
    (point : BasePoint) :
    canonicalSpacetimeContactTranslation 0 point = point := by
  simp [canonicalSpacetimeContactTranslation]

/-- On the canonical time-zero slice, full spacetime translation reduces to
the existing spatial-contact translation. -/
theorem canonicalSpacetimeContactTranslation_timeZero
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint 0 space) point =
      canonicalSpatialContactTranslation space point := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpacetimeContactTranslation,
      canonicalSpatialContactTranslation, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- Pull one primitive holonomic current back to one full spacetime
occurrence.  Every field uses the same translation, so no sector can silently
change lineage or contact. -/
def fullyRecenterHolonomicConfiguration
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration where
  coframe := fun point =>
    current.coframe (canonicalSpacetimeContactTranslation contact point)
  gravityConnection := fun point =>
    current.gravityConnection
      (canonicalSpacetimeContactTranslation contact point)
  gravityAuxiliary := fun point =>
    current.gravityAuxiliary
      (canonicalSpacetimeContactTranslation contact point)
  gravitySimplicityMultiplier := fun point =>
    current.gravitySimplicityMultiplier
      (canonicalSpacetimeContactTranslation contact point)
  gaugeConnection := fun point =>
    current.gaugeConnection
      (canonicalSpacetimeContactTranslation contact point)
  gaugeAuxiliary := fun point =>
    current.gaugeAuxiliary
      (canonicalSpacetimeContactTranslation contact point)
  scalar := fun point =>
    current.scalar (canonicalSpacetimeContactTranslation contact point)
  matter := fun point =>
    current.matter (canonicalSpacetimeContactTranslation contact point)
  conjugateMatter := fun point =>
    current.conjugateMatter
      (canonicalSpacetimeContactTranslation contact point)

@[simp] theorem fullyRecenterHolonomicConfiguration_conjugateMatter
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).conjugateMatter =
      current.conjugateMatter ∘ canonicalSpacetimeContactTranslation contact :=
  rfl

@[simp] theorem fullyRecenterHolonomicConfiguration_zero
    (current : StageNineHolonomicConfiguration) :
    fullyRecenterHolonomicConfiguration current 0 = current := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp [fullyRecenterHolonomicConfiguration]

/-- The primitive coframe value at the local origin is the value of the same
input field at the selected occurrence. -/
@[simp] theorem fullyRecenterHolonomicConfiguration_coframe_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).coframe 0 =
      current.coframe contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_gravityConnection_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).gravityConnection 0 =
      current.gravityConnection contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_gravityAuxiliary_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).gravityAuxiliary 0 =
      current.gravityAuxiliary contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem
    fullyRecenterHolonomicConfiguration_gravitySimplicityMultiplier_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).gravitySimplicityMultiplier
        0 =
      current.gravitySimplicityMultiplier contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_gaugeConnection_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).gaugeConnection 0 =
      current.gaugeConnection contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).gaugeAuxiliary 0 =
      current.gaugeAuxiliary contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_scalar_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).scalar 0 =
      current.scalar contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_matter_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).matter 0 =
      current.matter contact := by
  simp [fullyRecenterHolonomicConfiguration]

@[simp] theorem fullyRecenterHolonomicConfiguration_conjugateMatter_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).conjugateMatter 0 =
      current.conjugateMatter contact := by
  simp [fullyRecenterHolonomicConfiguration]

/-- The full recentering preserves the supplied current's explicit smooth
field regularity. -/
theorem fullyRecenterHolonomicConfiguration_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (contact : BasePoint) :
    (fullyRecenterHolonomicConfiguration current contact).Smooth := by
  have translationSmooth :
      ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation contact) := by
    unfold canonicalSpacetimeContactTranslation
    fun_prop
  rcases smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩
  exact
    ⟨fun row column => by
        change ContDiff ℝ ∞
          ((fun point => current.coframe point row column) ∘
            canonicalSpacetimeContactTranslation contact)
        exact (coframe row column).comp translationSmooth,
      fun direction internalOut internalIn => by
        change ContDiff ℝ ∞
          ((fun point => current.gravityConnection point direction
            internalOut internalIn) ∘
              canonicalSpacetimeContactTranslation contact)
        exact (gravityConnection direction internalOut internalIn).comp
          translationSmooth,
      fun internalPair spacetimePair => by
        change ContDiff ℝ ∞
          ((fun point => current.gravityAuxiliary point internalPair
            spacetimePair) ∘ canonicalSpacetimeContactTranslation contact)
        exact (gravityAuxiliary internalPair spacetimePair).comp
          translationSmooth,
      fun internalPair spacetimePair => by
        change ContDiff ℝ ∞
          ((fun point => current.gravitySimplicityMultiplier point
            internalPair spacetimePair) ∘
              canonicalSpacetimeContactTranslation contact)
        exact (multiplier internalPair spacetimePair).comp translationSmooth,
      fun direction => by
        change ContDiff ℝ ∞
          ((fun point => p286CoordinateEquiv
            (current.gaugeConnection point direction)) ∘
              canonicalSpacetimeContactTranslation contact)
        exact (gaugeConnection direction).comp translationSmooth,
      fun pair => by
        change ContDiff ℝ ∞
          ((fun point => p286CoordinateEquiv
            (current.gaugeAuxiliary point pair)) ∘
              canonicalSpacetimeContactTranslation contact)
        exact (gaugeAuxiliary pair).comp translationSmooth,
      by
        change ContDiff ℝ ∞
          (current.scalar ∘ canonicalSpacetimeContactTranslation contact)
        exact scalar.comp translationSmooth,
      by
        change ContDiff ℝ ∞
          ((fun point => matterCoordinateEquiv (current.matter point)) ∘
            canonicalSpacetimeContactTranslation contact)
        exact matter.comp translationSmooth,
      fun index => by
        change ContDiff ℝ ∞
          ((fun point => current.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index 1))) ∘
                canonicalSpacetimeContactTranslation contact)
        exact (conjugateMatter index).comp translationSmooth⟩

/-- Full recentering at a time-zero occurrence is literally the established
spatial recentering used by the current complete-joint global section. -/
theorem fullyRecenterHolonomicConfiguration_timeZero
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    fullyRecenterHolonomicConfiguration current
        (canonicalCauchySlicePoint 0 space) =
      spatiallyRecenterHolonomicConfiguration current space := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp [fullyRecenterHolonomicConfiguration,
      spatiallyRecenterHolonomicConfiguration,
      canonicalSpacetimeContactTranslation_timeZero]

/-! ## Occurrence-native complete-joint contact -/

/-- The internal complete-joint action contact generated at a physical
spacetime occurrence.  It first recenters one current, then recomputes the
same Cartan restart and M/S/P/E action legs used by the global producer. -/
def completeJointActionFullOccurrenceContact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointActionResponseOperator source
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      (fullyRecenterHolonomicConfiguration current contact))

/-- At time zero the full-occurrence action contact agrees with the existing
spatial action contact, preserving the already-paid fixed P506/L0 proof chain. -/
theorem completeJointActionFullOccurrenceContact_timeZero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    completeJointActionFullOccurrenceContact source current
        (canonicalCauchySlicePoint 0 space) =
      completeJointActionSpatialContact source current space := by
  rw [completeJointActionFullOccurrenceContact,
    completeJointActionSpatialContact,
    fullyRecenterHolonomicConfiguration_timeZero]

/-- The complete action jet generated by the canonical recentered action leg
at the occurrence's local origin.  This is the family a later global field
lift must realize; it is not a residual or a supplied target. -/
def completeJointActionFullOccurrenceActionJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet source
    (completeJointActionFullOccurrenceContact source current contact) 0

theorem completeJointActionFullOccurrenceActionJet_timeZero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    completeJointActionFullOccurrenceActionJet source current
        (canonicalCauchySlicePoint 0 space) =
      generatedDiracDualFormNativePointwiseActionJet source
        (completeJointActionSpatialContact source current space) 0 := by
  rw [completeJointActionFullOccurrenceActionJet,
    completeJointActionFullOccurrenceContact_timeZero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
