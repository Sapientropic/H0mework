import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Revision.Source.SourceGeneratedPlatformChannelRevisionCandidate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Bootstrap.SourceGeneratedPostSettlementObserverSubmissionBootstrap

/-!
# Cross-occurrence transporter from cycle memory to the paid U8 visit

The relation recurrence and the post-settlement Payment are different actual
occurrences.  This file does not identify them.  It presents their exact
singleton lineage restrictions and proves that both carry the same existing
UBI restriction.  The presentation plus this common authority carrier is the
lawful transporter used by the platform-gate revision.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedCrossCompilerRelationAppendUBI
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate

/-- Exact restriction of the cross-compiler occurrence which generates the
platform-rooted cycle-memory obstruction. -/
abbrev PlatformGateRelationOccurrenceRestrictionAt (boundary : Nat) :=
  { occurrence : type_of%
      (appendStageAt (platformCycleBaseAfter boundary)).exactSource.occurrence //
    occurrence =
      (appendStageAt (platformCycleBaseAfter boundary)).exactSource.occurrence }

/-- Exact restriction of the distinct paid root occurrence which carries the
U8 update. -/
abbrev PlatformGatePaymentOccurrenceRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : type_of%
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence.occurrence //
    occurrence =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence.occurrence }

/-- The two exact lineage restrictions are constructively equivalent without
collapsing their ambient occurrence types. -/
def platformGateOccurrenceRestrictionPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (PlatformGateRelationOccurrenceRestrictionAt boundary)
      (PlatformGatePaymentOccurrenceRestrictionAt oldVisit sourceIndex
        boundary) where
  forward := fun _ => ⟨_, rfl⟩
  backward := fun _ => ⟨_, rfl⟩
  backward_forward := by
    intro occurrence
    apply Subtype.ext
    exact occurrence.property.symm
  forward_backward := by
    intro occurrence
    apply Subtype.ext
    exact occurrence.property.symm

/-- A lawful cross-occurrence transporter.  Its presentation acts only on
exact lineage restrictions; the common UBI restriction, not an occurrence
equality, transports authority between the two ambient roots. -/
structure SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 31 where
  private mk ::
  obstruction :
    SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary
  candidate : SourceGeneratedPlatformChannelRevisionCandidateAt boundary
  occurrencePresentation : ConstructivePresentation
    (PlatformGateRelationOccurrenceRestrictionAt boundary)
    (PlatformGatePaymentOccurrenceRestrictionAt oldVisit sourceIndex boundary)
  relationUBIExact :
    HEq
      (crossCompilerUBIPayloadAt
        (platformCycleBaseAfter boundary + 3)).consumer
      sourceGeneratedUBIRootRestriction
  paymentInstalledExact :
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.installed =
      installedUBIAt (rightCurrentAt oldVisit sourceIndex boundary)
  paymentUBIExact :
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.installed.payload.consumer =
      sourceGeneratedUBIRootRestriction
  paymentRootOccurrenceExact :
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary))

def sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
      oldVisit sourceIndex boundary where
  obstruction :=
    sourceGeneratedCycleMemoryPlatformGateObstructionAt boundary
  candidate := sourceGeneratedPlatformChannelRevisionCandidateAt boundary
  occurrencePresentation :=
    platformGateOccurrenceRestrictionPresentationAt oldVisit sourceIndex
      boundary
  relationUBIExact :=
    crossCompilerUBIPayloadConsumer_exact
      (platformCycleBaseAfter boundary + 3)
  paymentInstalledExact :=
    (rootedBridgeAt oldVisit sourceIndex boundary).rightPaymentInstalled_exact
  paymentUBIExact :=
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.exactRestriction
  paymentRootOccurrenceExact :=
    rightPaymentRootOccurrence_exact oldVisit sourceIndex boundary

theorem platformGatePaymentLineageTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (cycleMemoryPlatformGateObstruction_directConsumer boundary) ∧
      type_of% (platformChannelRevisionCandidate_directConsumer boundary) ∧
      Nonempty (ConstructivePresentation
        (PlatformGateRelationOccurrenceRestrictionAt boundary)
        (PlatformGatePaymentOccurrenceRestrictionAt oldVisit sourceIndex
          boundary)) ∧
      HEq
        (crossCompilerUBIPayloadAt
          (platformCycleBaseAfter boundary + 3)).consumer
        sourceGeneratedUBIRootRestriction ∧
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.installed.payload.consumer =
        sourceGeneratedUBIRootRestriction ∧
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) := by
  let transport :=
    sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
      oldVisit sourceIndex boundary
  exact ⟨cycleMemoryPlatformGateObstruction_directConsumer boundary,
    platformChannelRevisionCandidate_directConsumer boundary,
    ⟨transport.occurrencePresentation⟩,
    transport.relationUBIExact,
    transport.paymentUBIExact,
    transport.paymentRootOccurrenceExact⟩

end
end M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport.platformGateOccurrenceRestrictionPresentationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport.sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport.platformGatePaymentLineageTransport_directConsumer
