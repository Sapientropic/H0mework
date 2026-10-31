import H0mework.Foundation.Runtime.OperationalSeparation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Interface.SourceNativeM12SharedKernelCoordinates
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.Source.SourceGeneratedM12BeautyMaterial
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityRootSource

/-!
# Source-generated M12 aesthetic public communication

The honest source-state publication is realized as one actual contact event.
Its whole-carrier presentation transports the recipient from the coarse
context to the refined context; the fixed payload starts at coarse, the
generated path writes back refined, and the target consumer recomputes the
public proposal from the transported alignment.

This is an actual contact/path/trace/write-back chain over the existing M10
world support.  It is not the mere tuple of two observer readouts and does not
claim a cross-support cultural transmission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Beauty
namespace M12
namespace SharedKernel
namespace Communication

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M10OccurrenceCapacityRootSourceFixture
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel

noncomputable section

def contextSwap : SourceGeneratedM12AestheticContextOccurrence →
    SourceGeneratedM12AestheticContextOccurrence
  | .coarse => .refined
  | .refined => .coarse

@[simp] theorem contextSwap_involutive
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    contextSwap (contextSwap context) = context := by
  cases context <;> rfl

/-- Whole recipient-context presentation carried by the exact publication
contact. -/
def contextSwapPresentation : ConstructivePresentation
    SourceGeneratedM12AestheticContextOccurrence
    SourceGeneratedM12AestheticContextOccurrence where
  forward := contextSwap
  backward := contextSwap
  backward_forward := contextSwap_involutive
  forward_backward := contextSwap_involutive

/-- Private actual contact seal.  Its only evidence is the already generated
source-state kernel refinement; no target alignment or proposal is stored. -/
structure SourceGeneratedM12PublicationContact : Type where
  private mk ::
  refinement : type_of% coarseMiddleKernelRefinement

def sourceGeneratedM12PublicationContact :
    SourceGeneratedM12PublicationContact :=
  ⟨coarseMiddleKernelRefinement⟩

/-- One same-support communication algebra.  The event is actual even though
both endpoints live on the one M10 world support. -/
def m12AestheticCommunication : ActualCommunicationNetwork N where
  Carrier := fun _support => SourceGeneratedM12AestheticContextOccurrence
  Observation := fun _support => M12AestheticAlignmentReadout
  observe := fun _support context => sourceAlignmentRead context
  ContactAt := fun _sourceAnchor _targetAnchor =>
    SourceGeneratedM12PublicationContact
  IncidenceTransportAt := fun _sourceIncidence _targetIncidence => PUnit
  LineageTransportAt := fun _sourceLineage _targetLineage => PUnit
  Event := SourceGeneratedM12PublicationContact
  sourceSupport := fun _event => ()
  targetSupport := fun _event => ()
  contact := fun event => event
  incidenceTransport := fun _event => PUnit.unit
  lineageTransport := fun _event => PUnit.unit
  carrierTransport := fun _event => contextSwapPresentation

def m12PublicationPayloadSource :
    ActualPayloadSource m12AestheticCommunication where
  EventAt := fun _support => PUnit
  emit := fun _support => PUnit.unit
  payload := fun {_support} _event => .coarse

def m12PublicationTargetConsumer :
    ActualTargetConsumerSource m12AestheticCommunication where
  EventAt := fun _support _observation => PUnit
  emit := fun _support _observation => PUnit.unit
  EffectAt := fun _support => M12PublicAestheticProposal
  effectFromObservation := fun _support observation =>
    publicProposalOfEvaluation observation.phase
  openEntryAt := fun {_support} {_observation} _event =>
    ⟨(), PUnit.unit⟩

/-- No cut event is admitted in this positive one-contact fixture. -/
def m12PublicationSources :
    ActualOperationalSeparationSources m12AestheticCommunication where
  payloadSource := m12PublicationPayloadSource
  consumerSource := m12PublicationTargetConsumer
  CutEventAt := fun _source _target => PEmpty
  cutSide := fun event => nomatch event
  cut_source_side := fun event => nomatch event
  cut_target_side := fun event => nomatch event
  cut_blocks := fun event => nomatch event
  cutObstruction := fun event => nomatch event

def m12PublicationContactEdge :
    ActualContactEdgeAt m12AestheticCommunication () () :=
  ActualContactEdgeAt.canonical sourceGeneratedM12PublicationContact

def m12PublicationTail :
    SourceOwnedTransportPath m12AestheticCommunication () () :=
  @SourceOwnedTransportPath.nil N m12AestheticCommunication ()

def m12PublicationPath :
    SourceOwnedTransportPath m12AestheticCommunication () () :=
  @SourceOwnedTransportPath.cons N m12AestheticCommunication
    () () () m12PublicationContactEdge m12PublicationTail

def m12PublicDelivery : GeneratedDeliveryAt
    m12AestheticCommunication m12PublicationSources () () where
  path := m12PublicationPath

@[simp] theorem m12PublicationPath_length :
    m12PublicationPath.length = 1 :=
  rfl

@[simp] theorem m12PublicationPath_events :
    m12PublicationPath.events = [sourceGeneratedM12PublicationContact] :=
  rfl

@[simp] theorem m12PublicDelivery_sourceValue :
    m12PublicDelivery.sourceValue = .coarse :=
  rfl

@[simp] theorem m12PublicDelivery_targetValue :
    m12PublicDelivery.targetValue = .refined :=
  rfl

@[simp] theorem m12PublicDelivery_targetObservation :
    m12PublicDelivery.targetObservation = sourceAlignmentRead .refined :=
  rfl

@[simp] theorem m12PublicDelivery_effect :
    m12PublicDelivery.effect =
      (M12PublicAestheticProposal.endorse : M12PublicAestheticProposal) := by
  change publicProposalOfEvaluation
      (sourceAlignmentRead .refined).phase = .endorse
  rw [sourceAlignmentRead_refined_phase]
  rfl

theorem m12PublicDelivery_writeBack_exact :
    m12PublicDelivery.writeBack =
      m12PublicDelivery.path.generatedWriteBack
        m12PublicDelivery.sourceValue :=
  rfl

theorem m12PublicDelivery_target_eq_transport :
    m12PublicDelivery.targetValue =
      m12PublicationPath.transport m12PublicDelivery.sourceValue :=
  m12PublicDelivery.targetValue_eq_transport

theorem m12PublicDelivery_consumerSafe :
    ConsumerSafe
      (m12AestheticCommunication.observe ())
      (m12PublicationSources.consumerSource.consumerAt ()) :=
  m12PublicDelivery.observer_safe

/-- Before the actual publication contact, the same object carrier supports
different alignment phases.  This residual is consumed by the generated
contact rather than erased by a consensus label. -/
def m12PrePublicationAlignmentResidual :
    HiddenNullWitness sourceObjectRead
      (fun context => (sourceAlignmentRead context).phase) where
  left := .coarse
  right := .refined
  sameObservation := m12Beauty_object_preserved
  differentDisposition := by
    intro equality
    rw [sourceAlignmentRead_coarse_phase,
      sourceAlignmentRead_refined_phase] at equality
    cases equality

theorem m12PrePublicationAlignment_not_consumerSafe :
    ¬ ConsumerSafe sourceObjectRead
      (fun context => (sourceAlignmentRead context).phase) :=
  m12PrePublicationAlignmentResidual.not_consumerSafe

/-- After transport, speaker and recipient both recompute the refined phase;
the proposal is generated from that agreement. -/
theorem m12PostPublication_publicAgreement :
    (sourceAlignmentRead .refined).phase =
      m12PublicDelivery.targetObservation.phase ∧
      m12PublicDelivery.effect =
        (M12PublicAestheticProposal.endorse : M12PublicAestheticProposal) :=
  ⟨rfl, m12PublicDelivery_effect⟩

/-- The delivered effect is exactly the proposal recomputed on the shared
conditioned kernel, not a sibling policy bit. -/
theorem m12PublicDelivery_effect_eq_sharedKernelProposal :
    m12PublicDelivery.effect =
      sharedProposalFromVisible m12SharedConditionedVisible := by
  rw [m12PublicDelivery_effect]
  unfold sharedProposalFromVisible sharedEvaluationFromVisible
    sharedProbabilityFromVisible
  rw [m12Shared_conditioned_aboveHalf]
  rfl

theorem sourceGeneratedM12AestheticPublicCommunication_directConsumer :
    sourceGeneratedM12PublicationContact.refinement =
        coarseMiddleKernelRefinement ∧
      m12PublicationPath.length = 1 ∧
      m12PublicationPath.events =
        [sourceGeneratedM12PublicationContact] ∧
      m12PublicDelivery.sourceValue = .coarse ∧
      m12PublicDelivery.targetValue = .refined ∧
      type_of% m12PublicDelivery_writeBack_exact ∧
      type_of% m12PublicDelivery_target_eq_transport ∧
      m12PublicDelivery.effect =
        (M12PublicAestheticProposal.endorse : M12PublicAestheticProposal) ∧
      ConsumerSafe
        (m12AestheticCommunication.observe ())
        (m12PublicationSources.consumerSource.consumerAt ()) ∧
      Nonempty (HiddenNullWitness sourceObjectRead
        (fun context => (sourceAlignmentRead context).phase)) ∧
      type_of% m12PrePublicationAlignment_not_consumerSafe ∧
      type_of% m12PostPublication_publicAgreement ∧
      type_of% m12PublicDelivery_effect_eq_sharedKernelProposal :=
  ⟨rfl, m12PublicationPath_length, m12PublicationPath_events,
    m12PublicDelivery_sourceValue, m12PublicDelivery_targetValue,
    m12PublicDelivery_writeBack_exact,
    m12PublicDelivery_target_eq_transport,
    m12PublicDelivery_effect,
    m12PublicDelivery_consumerSafe,
    ⟨m12PrePublicationAlignmentResidual⟩,
    m12PrePublicationAlignment_not_consumerSafe,
    m12PostPublication_publicAgreement,
    m12PublicDelivery_effect_eq_sharedKernelProposal⟩

end
end Communication
end SharedKernel
end M12
end Beauty
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.contextSwapPresentation
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.m12PublicDelivery_writeBack_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.m12PrePublicationAlignmentResidual
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.sourceGeneratedM12AestheticPublicCommunication_directConsumer
