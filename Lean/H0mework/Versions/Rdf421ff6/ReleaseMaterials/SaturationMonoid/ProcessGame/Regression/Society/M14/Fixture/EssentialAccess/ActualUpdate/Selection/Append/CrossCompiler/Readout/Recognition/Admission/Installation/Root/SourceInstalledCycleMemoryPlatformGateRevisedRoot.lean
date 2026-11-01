import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Projection.SourceInstalledCycleMemoryPlatformGateRenewalProjection

/-!
# Richer revised root born with the cycle-memory platform gate

The already augmented observer-submission authority source receives the
source-generated platform-gate renewal face before emission.  The emitter,
compiler, occurrence, whole-ledger rows, first write and successor remain the
existing loss-allocation producers.  Thus the platform gate is installed on
the same actual first row rather than placed in a sibling root or ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport

def platformGateRevisedAuthoritativeRootAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := platformGateAuthoritySourceAt oldVisit sourceIndex boundary
  emitted := M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt
    (oldRootVisitAt oldVisit sourceIndex boundary)
  compiler_commutes :=
    M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_commutes
      (rootedAt (oldRootVisitAt oldVisit sourceIndex boundary))

def platformGateRevisedLivingRootAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source :=
    { base := platformGateAuthoritySourceAt oldVisit sourceIndex boundary
      terminalHandoff :=
        (platformGateAuthoritySourceAt oldVisit sourceIndex boundary
          ).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt
    (oldRootVisitAt oldVisit sourceIndex boundary)
  compiler_commutes :=
    M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_commutes
      (rootedAt (oldRootVisitAt oldVisit sourceIndex boundary))

def platformGateRevisedOccurrencePresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (rootedFailureAt oldVisit sourceIndex boundary).oldSuccessor.next)
      ((platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt (0 : Nat)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedOccurrencePresentationAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateRevisedFirstWriteAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    CanonicalFirstRootWriteAt
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedFirstWriteAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateInitialGeneratedEvolutionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot
      (.finite
        (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
          ).toRoot.initialVisit) :=
  (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLedgerRoot.generatedAtTemporalVisit
      (.finite
        (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
          ).toRoot.initialVisit)

def platformGateOldEntryRowAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (platformGateInitialGeneratedEvolutionAt oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
      (M9ProofCarryingRenewalU8RevisedLedger.oldRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedOldEntryRowAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateNewEntryRowAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (platformGateInitialGeneratedEvolutionAt oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
      (M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateRenewalRecognitionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalRecognitionAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary) PlatformGateSeed
      (PlatformGateSeedAt oldVisit sourceIndex boundary)
      (PlatformGateConsumerAt oldVisit sourceIndex boundary)
      (PlatformGateDispositionAt oldVisit sourceIndex boundary) where
  law := platformGateRenewalLawAt oldVisit sourceIndex boundary
  installation := platformGateInstallationAt oldVisit sourceIndex boundary

/-- The previously installed observer-submission coordinate survives through
the faithful inherited branch of the platform-gate uplift. -/
def inheritedSubmissionInstallationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary
        ).toProjectionLaw
      (platformGateAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  (augmentedSubmissionInstallationAt oldVisit sourceIndex boundary).trans
    (inheritedByRenewal
      (augmentedAuthoritySourceAt oldVisit sourceIndex boundary)
      (platformGateRenewalLawAt oldVisit sourceIndex boundary))

def inheritedSubmissionRecognitionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalRecognitionAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary)
      M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalSeed
      (M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalSeedAt
        oldVisit sourceIndex boundary)
      (M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalConsumerAt
        oldVisit sourceIndex boundary)
      (M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalDispositionAt
        oldVisit sourceIndex boundary) where
  law := augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary
  installation := inheritedSubmissionInstallationAt oldVisit sourceIndex
    boundary

def platformGateInitialVisitAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.initialVisit

def platformGateInstalledRenewalAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceInstalledRenewalAt
      (platformGateRenewalRecognitionAt oldVisit sourceIndex boundary)
      (platformGateInitialVisitAt oldVisit sourceIndex boundary) :=
  SourceInstalledRenewalAt.generate ⟨rfl⟩ (by
    change
      (platformGateRenewalLawAt oldVisit sourceIndex boundary).classify
          ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
            ).emitted (0 : Nat)) =
        .inl ⟨rfl⟩
    simp [platformGateRenewalLawAt,
      SourceNativeRenewalProjectionLaw.ofRootShell,
      platformGateRootShellAt])

def inheritedSubmissionInstalledRenewalAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceInstalledRenewalAt
      (inheritedSubmissionRecognitionAt oldVisit sourceIndex boundary)
      (platformGateInitialVisitAt oldVisit sourceIndex boundary) :=
  SourceInstalledRenewalAt.generate ⟨rfl⟩ (by
    change
      (augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary).classify
          ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
            ).emitted (0 : Nat)) =
        .inl ⟨rfl⟩
    simp [augmentedSubmissionRenewalLawAt,
      SourceNativeRenewalProjectionLaw.ofRootShell,
      augmentedSubmissionRootShellAt])

@[simp] theorem platformGate_sourceEntry_eq_existingNewOnlyEntry
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).payload.sourceEntry =
      (M9ProofCarryingRenewalU8RevisedWorld.generatedTypedRevisionAt
        (oldRootVisitAt oldVisit sourceIndex boundary)).newOnlyEntry :=
  rfl

theorem platformGate_selectedRow_heq_existingNewOnlyRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.selectedRow
      (M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
        (oldRootVisitAt oldVisit sourceIndex boundary)).sourceRow :=
  HEq.rfl

theorem platformGate_successor_heq_existingFirstSuccessor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.successor
      (M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  HEq.rfl

theorem platformGateInstalledPayload_carriesPaymentLineageTransport
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty
      (SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
        oldVisit sourceIndex boundary) :=
  (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
    ).payload.consumer.down

@[simp] theorem platformGateInstalledPayload_consumer_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).payload.consumer =
      platformGateConsumer oldVisit sourceIndex boundary :=
  rfl

theorem platformGateInstalledPayload_carriesRevisionCandidate
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty
      (SourceGeneratedPlatformChannelRevisionCandidateAt boundary) :=
  (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
    ).payload.disposition.down

@[simp] theorem platformGateInstalledPayload_disposition_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).payload.disposition =
      platformGateDisposition oldVisit sourceIndex boundary :=
  rfl

theorem inheritedSubmissionPayload_carriesRootedAuthority
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty
      (SourceNativeObserverConsumerRootedAuthorityAt
        (canonicalSubmissionAt oldVisit sourceIndex boundary)) :=
  (inheritedSubmissionInstalledRenewalAt oldVisit sourceIndex boundary
    ).payload.disposition.down

theorem platformGateActualFirstEvent_projectionOutcome_heq_sourceLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (platformGateRenewalRecognitionAt oldVisit sourceIndex boundary
            ).rootProjection
          ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
            ).emitted (0 : Nat)))
      ((platformGateRenewalRecognitionAt oldVisit sourceIndex boundary
        ).law.toProjectionLaw.outcomeAt PUnit.unit
          ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
            ).emitted (0 : Nat))) :=
  (platformGateRenewalRecognitionAt oldVisit sourceIndex boundary
    ).componentOutcome_heq_rootOutcome
      ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).emitted (0 : Nat))

theorem platformGateInstalled_completeExistingFirstRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
        ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            (platformGateRenewalRecognitionAt oldVisit sourceIndex boundary
              ).rootProjection
            ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
              ).emitted (0 : Nat)))
        ((platformGateRenewalRecognitionAt oldVisit sourceIndex boundary
          ).law.toProjectionLaw.outcomeAt PUnit.unit
            ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
              ).emitted (0 : Nat))) ∧
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.sourceEntry =
        (M9ProofCarryingRenewalU8RevisedWorld.generatedTypedRevisionAt
          (oldRootVisitAt oldVisit sourceIndex boundary)).newOnlyEntry ∧
      HEq
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).payload.selectedRow
        (M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
          (oldRootVisitAt oldVisit sourceIndex boundary)).sourceRow ∧
      HEq
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).payload.successor
        (M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
          (oldRootVisitAt oldVisit sourceIndex boundary)) ∧
      Nonempty
        (SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
          oldVisit sourceIndex boundary) ∧
      Nonempty
        (SourceGeneratedPlatformChannelRevisionCandidateAt boundary) ∧
      Nonempty
        (SourceNativeObserverConsumerRootedAuthorityAt
          (canonicalSubmissionAt oldVisit sourceIndex boundary)) :=
  ⟨platformGateActualFirstEvent_projectionOutcome_heq_sourceLaw oldVisit
      sourceIndex boundary,
    platformGate_sourceEntry_eq_existingNewOnlyEntry oldVisit sourceIndex
      boundary,
    platformGate_selectedRow_heq_existingNewOnlyRow oldVisit sourceIndex
      boundary,
    platformGate_successor_heq_existingFirstSuccessor oldVisit sourceIndex
      boundary,
    platformGateInstalledPayload_carriesPaymentLineageTransport oldVisit
      sourceIndex boundary,
    platformGateInstalledPayload_carriesRevisionCandidate oldVisit
      sourceIndex boundary,
    inheritedSubmissionPayload_carriesRootedAuthority oldVisit sourceIndex
      boundary⟩

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRevisedAuthoritativeRootAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateInstalledRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateInstalled_completeExistingFirstRow
