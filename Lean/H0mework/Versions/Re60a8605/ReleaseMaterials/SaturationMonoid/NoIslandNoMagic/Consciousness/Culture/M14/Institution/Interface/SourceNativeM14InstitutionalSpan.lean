import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface.SourceNativeM14CultureCoordinates
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Transport.SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Consumer.ProofCarryingPlatformGateFullAdmission

/-!
# Source-native institutional span for the M14 culture chart

The platform relation occurrence is one fork point.  Its actual three-cycle
reaches the renewed material occurrence, while the existing singleton
presentation transports its exact restriction to the distinct right-Payment
occurrence carrying the paid platform U8.  These are two source branches, not
a fabricated Payment-to-material occurrence equality.

The low-universe codes below expose selection, observer/admission, and actual
material-service coordinates.  The high-universe transporter, paid U8, and
full-admission certificates remain only in the source span and grounding
mouth.  No institutional consumer family, culture carrier, quotient, root
installation, or successor is accepted as input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Institution
namespace Interface

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open ProcessGame.Society.M14EssentialAccessRelationFixture
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendStage
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation
open ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateObstruction
open ProcessGame.Society.M14SourceGeneratedPlatformChannelRevisionCandidate
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8
open ProcessGame.Society.M14SourceGeneratedPlatformGateAffectedBearerIncidence
open ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface

noncomputable section

/-! ## Exact culture/relation/material alignment -/

def m14InstitutionalBaseAt (boundary : Nat) : Nat :=
  platformCycleBaseAfter boundary

abbrev M14InstitutionalCultureOccurrenceAt (boundary : Nat) :=
  M14CultureOccurrenceAt (m14InstitutionalBaseAt boundary)

@[simp] theorem m14InstitutionalCultureDepth_false (boundary : Nat) :
    sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) false =
      platformGateAffectedBearerDepthAt boundary :=
  rfl

@[simp] theorem m14InstitutionalCultureDepth_true (boundary : Nat) :
    sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) true =
      platformGateMaterialDepthAt boundary :=
  rfl

theorem m14InstitutionalRelationMaterial_occurrences_distinct
    (boundary : Nat) :
    (crossCompilerActionPresentationAt
        (sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) true)
      ).erase ≠
      (crossCompilerActionPresentationAt
        (sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) false)
      ).erase := by
  simpa only [m14InstitutionalCultureDepth_true,
    m14InstitutionalCultureDepth_false] using
      platformGateMaterialOccurrence_distinctFromGate boundary

/-! ## The lawful relation-centered span -/

abbrev M14InstitutionalRelationOccurrenceAt (boundary : Nat) :=
  PlatformGateRelationOccurrenceRestrictionAt boundary

abbrev M14InstitutionalPaymentOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  PlatformGatePaymentOccurrenceRestrictionAt oldVisit sourceIndex boundary

abbrev M14InstitutionalMaterialOccurrenceAt (boundary : Nat) :=
  { occurrence : type_of%
      (appendStageAt (platformGateMaterialDepthAt boundary)
        ).exactSource.occurrence //
    occurrence =
      (appendStageAt (platformGateMaterialDepthAt boundary)
        ).exactSource.occurrence }

def m14InstitutionalRelationOccurrenceAt (boundary : Nat) :
    M14InstitutionalRelationOccurrenceAt boundary :=
  ⟨(appendStageAt (platformCycleBaseAfter boundary)).exactSource.occurrence,
    rfl⟩

def m14InstitutionalPaymentOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary :=
  ⟨((ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightReplayAt
      oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.rootOccurrence.occurrence, rfl⟩

def m14InstitutionalMaterialOccurrenceAt (boundary : Nat) :
    M14InstitutionalMaterialOccurrenceAt boundary :=
  ⟨(appendStageAt (platformGateMaterialDepthAt boundary)
      ).exactSource.occurrence, rfl⟩

inductive M14InstitutionalSpanNode where
  | relation
  | payment
  | material
  deriving DecidableEq, Repr

def M14InstitutionalSpanOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14InstitutionalSpanNode → Type
  | .relation => M14InstitutionalRelationOccurrenceAt boundary
  | .payment =>
      M14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary
  | .material => M14InstitutionalMaterialOccurrenceAt boundary

def m14InstitutionalSpanOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (node : M14InstitutionalSpanNode) →
      M14InstitutionalSpanOccurrenceAt oldVisit sourceIndex boundary node
  | .relation => m14InstitutionalRelationOccurrenceAt boundary
  | .payment =>
      m14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary
  | .material => m14InstitutionalMaterialOccurrenceAt boundary

@[simp] theorem m14InstitutionalRelationPaymentPresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateOccurrenceRestrictionPresentationAt oldVisit sourceIndex
      boundary).forward (m14InstitutionalRelationOccurrenceAt boundary) =
        m14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary :=
  rfl

/-! ## Low-universe institutional codes -/

structure M14InstitutionalSelectionCode : Type where
  relationDepth : Nat
  selectedEvent : EssentialAccessEvent
  materialDepth : Nat
  materialSelectedEvent : EssentialAccessEvent

def m14InstitutionalSelectionCodeAt (boundary : Nat) :
    M14InstitutionalSelectionCode where
  relationDepth := platformGateAffectedBearerDepthAt boundary
  selectedEvent :=
    ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.crossCompilerSelectedEventAt
      (platformGateAffectedBearerDepthAt boundary)
  materialDepth := platformGateMaterialDepthAt boundary
  materialSelectedEvent :=
    ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.crossCompilerSelectedEventAt
      (platformGateMaterialDepthAt boundary)

@[simp] theorem m14InstitutionalSelectionCode_events_platform
    (boundary : Nat) :
    (m14InstitutionalSelectionCodeAt boundary).selectedEvent = .platform ∧
      (m14InstitutionalSelectionCodeAt boundary).materialSelectedEvent =
        .platform :=
  ⟨platformGateAffectedBearer_selectedEvent_platform boundary,
    platformGateMaterialSelectedEvent_platform boundary⟩

structure M14InstitutionalAdmissionCode : Type where
  paymentCurrent : Nat
  rootCurrent : Nat
  platformSeed : essentialAccessRelationCompiler.ExactRelationSeed
  targetRole : EssentialAccessRole
  observerAuthorityInherited : Bool
  paidU8Installed : Bool

def m14InstitutionalAdmissionCodeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14InstitutionalAdmissionCode where
  paymentCurrent :=
    ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightCurrentAt
      oldVisit sourceIndex boundary
  rootCurrent := 0
  platformSeed := exactEssentialAccessSeed .platform
  targetRole := .platformProvider
  observerAuthorityInherited := true
  paidU8Installed := true

structure M14InstitutionalMaterialCode : Type where
  sourceDepth : Nat
  sourceBudget : Nat
  targetBudget : Nat
  eventCount : Nat
  selectedEvent : EssentialAccessEvent
  terminal : Bool
  reopenable : Bool

def m14InstitutionalMaterialCodeAt (boundary : Nat) :
    M14InstitutionalMaterialCode where
  sourceDepth := platformGateMaterialDepthAt boundary
  sourceBudget := platformGateMaterialBudgetAt
    (platformGateMaterialServiceSourceStateAt boundary) .debt
  targetBudget := platformGateMaterialBudgetAt
    (platformGateMaterialPostServiceStateAt boundary) .debt
  eventCount := (platformGateMaterialServiceRunAt boundary).events.length
  selectedEvent :=
    ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.crossCompilerSelectedEventAt
      (platformGateMaterialDepthAt boundary)
  terminal := true
  reopenable := false

@[simp] theorem m14InstitutionalMaterialCode_exact (boundary : Nat) :
    (m14InstitutionalMaterialCodeAt boundary).sourceBudget = 1 ∧
      (m14InstitutionalMaterialCodeAt boundary).targetBudget = 0 ∧
      (m14InstitutionalMaterialCodeAt boundary).eventCount = 1 ∧
      (m14InstitutionalMaterialCodeAt boundary).selectedEvent = .platform ∧
      (m14InstitutionalMaterialCodeAt boundary).terminal = true ∧
      (m14InstitutionalMaterialCodeAt boundary).reopenable = false :=
  ⟨platformGateMaterial_sourceBudget_eq_one boundary,
    platformGateMaterial_targetBudget_eq_zero boundary,
    platformGateMaterialServiceRun_events_length boundary,
    platformGateMaterialSelectedEvent_platform boundary, rfl, rfl⟩

/-! ## High source span and stable grounding mouths -/

structure SourceGeneratedM14InstitutionalSpanAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  relationOccurrence : M14InstitutionalRelationOccurrenceAt boundary
  relationOccurrenceExact : relationOccurrence =
    m14InstitutionalRelationOccurrenceAt boundary
  paymentOccurrence :
    M14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary
  paymentOccurrenceExact : paymentOccurrence =
    m14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary
  materialOccurrence : M14InstitutionalMaterialOccurrenceAt boundary
  materialOccurrenceExact : materialOccurrence =
    m14InstitutionalMaterialOccurrenceAt boundary
  paymentTransport :
    SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
      oldVisit sourceIndex boundary
  paymentTransportExact : paymentTransport =
    sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt oldVisit
      sourceIndex boundary
  materialService : SourceGeneratedPlatformGateRenewedActualServiceAt
    oldVisit sourceIndex boundary
  materialServiceExact : materialService =
    sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
      boundary
  fullAdmission : ProofCarryingPlatformGateFullAdmissionAt
    oldVisit sourceIndex boundary
  fullAdmissionExact : fullAdmission =
    proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary

def sourceGeneratedM14InstitutionalSpanAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex boundary where
  relationOccurrence := m14InstitutionalRelationOccurrenceAt boundary
  relationOccurrenceExact := rfl
  paymentOccurrence :=
    m14InstitutionalPaymentOccurrenceAt oldVisit sourceIndex boundary
  paymentOccurrenceExact := rfl
  materialOccurrence := m14InstitutionalMaterialOccurrenceAt boundary
  materialOccurrenceExact := rfl
  paymentTransport :=
    sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt oldVisit
      sourceIndex boundary
  paymentTransportExact := rfl
  materialService :=
    sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
      boundary
  materialServiceExact := rfl
  fullAdmission :=
    proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
  fullAdmissionExact := rfl

theorem sourceGeneratedM14InstitutionalPaidU8_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of%
      (proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
        sourceIndex boundary) :=
  proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit sourceIndex
    boundary

theorem sourceGeneratedM14InstitutionalFullAdmission_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (platformGateFullAdmission_directConsumer oldVisit sourceIndex
      boundary) :=
  platformGateFullAdmission_directConsumer oldVisit sourceIndex boundary

theorem sourceGeneratedM14InstitutionalSpan_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let span := sourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex
      boundary
    Nonempty (SourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex
        boundary) ∧
      sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) false =
        platformGateAffectedBearerDepthAt boundary ∧
      sourceM14CultureDepthAt (m14InstitutionalBaseAt boundary) true =
        platformGateMaterialDepthAt boundary ∧
      span.paymentTransport.occurrencePresentation.forward
          span.relationOccurrence = span.paymentOccurrence ∧
      type_of% (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
        (m14InstitutionalBaseAt boundary)) ∧
      type_of% (platformGatePaymentLineageTransport_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (platformGateRenewedActualService_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (platformGateFullAdmission_directConsumer oldVisit sourceIndex
        boundary) ∧
      type_of% (m14InstitutionalRelationMaterial_occurrences_distinct
        boundary) ∧
      type_of% (m14InstitutionalSelectionCode_events_platform boundary) ∧
      type_of% (m14InstitutionalMaterialCode_exact boundary) := by
  let span := sourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex
    boundary
  refine ⟨⟨span⟩, m14InstitutionalCultureDepth_false boundary,
    m14InstitutionalCultureDepth_true boundary, ?_,
    sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
      (m14InstitutionalBaseAt boundary),
    platformGatePaymentLineageTransport_directConsumer oldVisit sourceIndex
      boundary,
    platformGateRenewedActualService_directConsumer oldVisit sourceIndex
      boundary,
    platformGateFullAdmission_directConsumer oldVisit sourceIndex boundary,
    m14InstitutionalRelationMaterial_occurrences_distinct boundary,
    m14InstitutionalSelectionCode_events_platform boundary,
    m14InstitutionalMaterialCode_exact boundary⟩
  rw [span.paymentTransportExact, span.relationOccurrenceExact,
    span.paymentOccurrenceExact]
  exact m14InstitutionalRelationPaymentPresentation_commutes oldVisit
    sourceIndex boundary

end
end Interface
end Institution
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.m14InstitutionalCultureDepth_false
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.m14InstitutionalCultureDepth_true
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.m14InstitutionalRelationMaterial_occurrences_distinct
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.m14InstitutionalMaterialCode_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.sourceGeneratedM14InstitutionalSpan_directConsumer
