import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Source.SourceGeneratedM14PlatformTeachingDelivery
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.SourceGeneratedM14StructuralClassPriceCultureRepresentation

/-!
# Independent M14 teaching consumers

The occurrence domain is the exact source and target practice of the generated
one-edge material-action delivery.  Both sides are restricted to the same
complete class-price culture face; teaching transmission and evaluation are
declared independently before any teaching carrier or quotient.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Teaching
namespace Consumer

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle
open ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual
open ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Source

noncomputable section

abbrev M14TeachingSourceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { practice : M14TeachingPracticeAt boundary .t0 //
    practice =
      (m14TeachingDeliveryAt oldVisit sourceIndex boundary).sourceValue }

abbrev M14TeachingTargetOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { practice : M14TeachingPracticeAt boundary .t1 //
    practice =
      (m14TeachingDeliveryAt oldVisit sourceIndex boundary).targetValue }

abbrev M14TeachingOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary ⊕
    M14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary

def m14TeachingSourceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary :=
  .inl ⟨(m14TeachingDeliveryAt oldVisit sourceIndex boundary).sourceValue,
    rfl⟩

def m14TeachingTargetOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary :=
  .inr ⟨(m14TeachingDeliveryAt oldVisit sourceIndex boundary).targetValue,
    rfl⟩

def m14TeachingContextReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM12AestheticContextOccurrence
  | .inl occurrence => occurrence.1.2
  | .inr occurrence => occurrence.1.2

structure M14TeachingTransmissionReadout : Type where
  support : ThreeCycleTime
  role : ProcessGame.Society.M14EssentialAccessRelationFixture.EssentialAccessRole
  context : SourceGeneratedM12AestheticContextOccurrence
  alignment : M12AestheticAlignmentReadout

def m14TeachingTransmissionReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
      M14TeachingTransmissionReadout
  | .inl occurrence =>
      { support := .t0
        role := occurrence.1.1.1
        context := occurrence.1.2
        alignment := sourceAlignmentRead occurrence.1.2 }
  | .inr occurrence =>
      { support := .t1
        role := occurrence.1.1.1
        context := occurrence.1.2
        alignment := sourceAlignmentRead occurrence.1.2 }

def m14TeachingEvaluationReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary → M14TeachingEffect
  | .inl occurrence =>
      { incomingRoleScore := actualRelationIncomingRoleReadAt
          (m14TeachingDepthAt boundary) .t0 occurrence.1.1.1
        proposal := publicProposalOfEvaluation
          (sourceAlignmentRead occurrence.1.2).phase }
  | .inr occurrence =>
      { incomingRoleScore := actualRelationIncomingRoleReadAt
          (m14TeachingDepthAt boundary) .t1 occurrence.1.1.1
        proposal := publicProposalOfEvaluation
          (sourceAlignmentRead occurrence.1.2).phase }

def m14TeachingOldClassPriceViewAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
      M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary :=
  fun _occurrence =>
    m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary

def m14TeachingTransmissionIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14TeachingOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14TeachingTransmissionReadout
  read := m14TeachingTransmissionReadAt

def m14TeachingEvaluationIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14TeachingOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14TeachingEffect
  read := m14TeachingEvaluationReadAt

def m14TeachingReindexedClassPriceConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary).reindex
    (m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary)

def m14TeachingTransmissionConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingReindexedClassPriceConsumersAt oldVisit sourceIndex boundary
    ).adjoin
      (m14TeachingTransmissionIndependentReadoutAt oldVisit sourceIndex
        boundary)

def m14TeachingConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingTransmissionConsumersAt oldVisit sourceIndex boundary).adjoin
    (m14TeachingEvaluationIndependentReadoutAt oldVisit sourceIndex boundary)

@[simp] theorem m14TeachingOldClassPriceView_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) =
      m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) :=
  rfl

@[simp] theorem m14TeachingContextRead_source_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingContextReadAt
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) =
      .coarse :=
  m14TeachingDelivery_sourceContext oldVisit sourceIndex boundary

@[simp] theorem m14TeachingContextRead_target_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingContextReadAt
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) =
      .refined :=
  m14TeachingDelivery_targetContext oldVisit sourceIndex boundary

theorem m14TeachingContextRead_source_ne_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingContextReadAt
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14TeachingContextReadAt
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) := by
  rw [m14TeachingContextRead_source_exact,
    m14TeachingContextRead_target_exact]
  decide

theorem m14TeachingTransmissionRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14TeachingTransmissionReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary)) := by
  intro left right sameRead
  cases left with
  | inl leftSource =>
      cases right with
      | inl rightSource =>
          exact congrArg Sum.inl (Subtype.ext
            (leftSource.property.trans rightSource.property.symm))
      | inr rightTarget =>
          have sameContext := congrArg M14TeachingTransmissionReadout.context
            sameRead
          have leftExact := congrArg Prod.snd leftSource.property
          have rightExact := congrArg Prod.snd rightTarget.property
          have impossible :
              SourceGeneratedM12AestheticContextOccurrence.coarse =
                .refined := by
            exact (m14TeachingDelivery_sourceContext oldVisit sourceIndex
              boundary).symm.trans
                (leftExact.symm.trans
                  (sameContext.trans
                    (rightExact.trans
                      (m14TeachingDelivery_targetContext oldVisit sourceIndex
                        boundary))))
          cases impossible
  | inr leftTarget =>
      cases right with
      | inl rightSource =>
          have sameContext := congrArg M14TeachingTransmissionReadout.context
            sameRead
          have leftExact := congrArg Prod.snd leftTarget.property
          have rightExact := congrArg Prod.snd rightSource.property
          have impossible :
              SourceGeneratedM12AestheticContextOccurrence.coarse =
                .refined := by
            exact (m14TeachingDelivery_sourceContext oldVisit sourceIndex
              boundary).symm.trans
                (rightExact.symm.trans
                  (sameContext.symm.trans
                    (leftExact.trans
                      (m14TeachingDelivery_targetContext oldVisit sourceIndex
                        boundary))))
          cases impossible
      | inr rightTarget =>
          exact congrArg Sum.inr (Subtype.ext
            (leftTarget.property.trans rightTarget.property.symm))

theorem m14TeachingTransmissionRead_source_ne_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingTransmissionReadAt
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14TeachingTransmissionReadAt
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) := by
  intro sameRead
  exact m14TeachingContextRead_source_ne_target oldVisit sourceIndex boundary
    (congrArg M14TeachingTransmissionReadout.context sameRead)

theorem m14TeachingEvaluationRead_source_ne_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingEvaluationReadAt
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14TeachingEvaluationReadAt
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) := by
  intro sameRead
  have sameProposal := congrArg M14TeachingEffect.proposal sameRead
  change publicProposalOfEvaluation (sourceAlignmentRead .coarse).phase =
    publicProposalOfEvaluation (sourceAlignmentRead .refined).phase at sameProposal
  rw [sourceAlignmentRead_coarse_phase,
    sourceAlignmentRead_refined_phase] at sameProposal
  cases sameProposal

theorem m14TeachingTransmissionKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary)
      (m14TeachingTransmissionIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingOldClassPriceView_source_eq_target oldVisit sourceIndex
      boundary,
    m14TeachingTransmissionRead_source_ne_target oldVisit sourceIndex
      boundary⟩

theorem m14TeachingEvaluationKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary)
      (m14TeachingEvaluationIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingOldClassPriceView_source_eq_target oldVisit sourceIndex
      boundary,
    m14TeachingEvaluationRead_source_ne_target oldVisit sourceIndex boundary⟩

structure M14TeachingWithoutTraceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  noEvents : (m14TeachingPathAt oldVisit sourceIndex boundary).events = []

theorem m14TeachingWithoutTrace_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty (M14TeachingWithoutTraceAt oldVisit sourceIndex boundary) :=
  ⟨fun forged => by
    have noEvents := forged.noEvents
    rw [m14TeachingPath_events_exact] at noEvents
    cases noEvents⟩

structure M14TeachingReadOnlyWithoutWriteBackAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  noWriteBack : IsEmpty
    (type_of% (m14TeachingDeliveryAt oldVisit sourceIndex boundary).writeBack)

theorem m14TeachingReadOnlyWithoutWriteBack_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty
      (M14TeachingReadOnlyWithoutWriteBackAt oldVisit sourceIndex boundary) :=
  ⟨fun forged => forged.noWriteBack.false
    (m14TeachingDeliveryAt oldVisit sourceIndex boundary).writeBack⟩

theorem m14TeachingConsumer_grounded
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14PlatformTeachingDelivery_directConsumer
      oldVisit sourceIndex boundary) ∧
      Function.Injective
        (m14TeachingTransmissionReadAt (oldVisit := oldVisit)
          (sourceIndex := sourceIndex) (boundary := boundary)) ∧
      type_of% (m14TeachingTransmissionKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingEvaluationKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      IsEmpty (M14TeachingWithoutTraceAt oldVisit sourceIndex boundary) ∧
      IsEmpty
        (M14TeachingReadOnlyWithoutWriteBackAt oldVisit sourceIndex
          boundary) :=
  ⟨sourceGeneratedM14PlatformTeachingDelivery_directConsumer oldVisit
      sourceIndex boundary,
    m14TeachingTransmissionRead_injective oldVisit sourceIndex boundary,
    m14TeachingTransmissionKernelEscapeAt oldVisit sourceIndex boundary,
    m14TeachingEvaluationKernelEscapeAt oldVisit sourceIndex boundary,
    m14TeachingWithoutTrace_isEmpty oldVisit sourceIndex boundary,
    m14TeachingReadOnlyWithoutWriteBack_isEmpty oldVisit sourceIndex
      boundary⟩

end
end Consumer
end Teaching
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer.m14TeachingTransmissionRead_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer.m14TeachingTransmissionKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer.m14TeachingEvaluationKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer.m14TeachingConsumer_grounded
