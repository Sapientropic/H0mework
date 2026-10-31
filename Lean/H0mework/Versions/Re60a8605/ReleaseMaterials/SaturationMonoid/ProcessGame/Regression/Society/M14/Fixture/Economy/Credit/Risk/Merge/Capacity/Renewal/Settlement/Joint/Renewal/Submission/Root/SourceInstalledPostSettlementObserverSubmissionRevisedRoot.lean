import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Projection.SourceInstalledPostSettlementObserverSubmissionRenewalProjection

/-!
# Richer revised root born with the observer-submission face

The authority inventory is augmented before the emitter is supplied.  The
emitter, ledger compiler, rows and successor remain the existing M9
visit-polymorphic loss-allocation producers.  Submission authority is a
dependent face of their first actual row, not a replacement ledger meaning.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource

def augmentedRevisedAuthoritativeRootAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := augmentedAuthoritySourceAt oldVisit sourceIndex boundary
  emitted := M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt
    (oldRootVisitAt oldVisit sourceIndex boundary)
  compiler_commutes :=
    M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_commutes
      (rootedAt (oldRootVisitAt oldVisit sourceIndex boundary))

def augmentedRevisedLivingRootAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source :=
    { base := augmentedAuthoritySourceAt oldVisit sourceIndex boundary
      terminalHandoff :=
        (augmentedAuthoritySourceAt oldVisit sourceIndex boundary
          ).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt
    (oldRootVisitAt oldVisit sourceIndex boundary)
  compiler_commutes :=
    M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_commutes
      (rootedAt (oldRootVisitAt oldVisit sourceIndex boundary))

def revisedAuthoritativeRootAt := augmentedRevisedAuthoritativeRootAt
def revisedLivingRootAt := augmentedRevisedLivingRootAt

def augmentedRevisedOccurrencePresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (rootedFailureAt oldVisit sourceIndex boundary).oldSuccessor.next)
      ((augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt (0 : Nat)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedOccurrencePresentationAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedRevisedFirstWriteAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    CanonicalFirstRootWriteAt
      (augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedFirstWriteAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedInitialGeneratedEvolutionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot
      (.finite
        (augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
          ).toRoot.initialVisit) :=
  (augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLedgerRoot.generatedAtTemporalVisit
      (.finite
        (augmentedRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
          ).toRoot.initialVisit)

def augmentedOldEntryRowAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (augmentedInitialGeneratedEvolutionAt oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
      (M9ProofCarryingRenewalU8RevisedLedger.oldRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedOldEntryRowAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedNewEntryRowAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (augmentedInitialGeneratedEvolutionAt oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
      (M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedRenewalRecognitionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalRecognitionAt
      (augmentedRevisedLivingRootAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary) LocalSeed
      (LocalSeedAt oldVisit sourceIndex boundary)
      (LocalConsumerAt oldVisit sourceIndex boundary)
      (LocalDispositionAt oldVisit sourceIndex boundary) where
  law := augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary
  installation := augmentedSubmissionInstallationAt oldVisit sourceIndex boundary

def augmentedInitialVisitAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (augmentedRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (augmentedRevisedLivingRootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.initialVisit

def augmentedInstalledRenewalAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceInstalledRenewalAt
      (augmentedRenewalRecognitionAt oldVisit sourceIndex boundary)
      (augmentedInitialVisitAt oldVisit sourceIndex boundary) :=
  SourceInstalledRenewalAt.generate ⟨rfl⟩ (by
    change
      (augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary).classify
          ((augmentedRevisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (0 : Nat)) =
        .inl ⟨rfl⟩
    simp [augmentedSubmissionRenewalLawAt,
      SourceNativeRenewalProjectionLaw.ofRootShell,
      augmentedSubmissionRootShellAt])

def renewalRecognitionAt := augmentedRenewalRecognitionAt
def activatedSubmissionAt := augmentedInstalledRenewalAt

/-- The face is attached to the richer revision's existing new-only first
row.  This theorem makes no claim that submission generated that row. -/
@[simp] theorem augmentedSubmission_sourceEntry_eq_existingNewOnlyEntry
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((augmentedInstalledRenewalAt oldVisit sourceIndex boundary).payload
      ).sourceEntry =
      (M9ProofCarryingRenewalU8RevisedWorld.generatedTypedRevisionAt
        (oldRootVisitAt oldVisit sourceIndex boundary)).newOnlyEntry :=
  rfl

theorem augmentedSubmission_selectedRow_heq_existingNewOnlyRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((augmentedInstalledRenewalAt oldVisit sourceIndex boundary).payload
        ).selectedRow
      (M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
        (oldRootVisitAt oldVisit sourceIndex boundary)).sourceRow :=
  HEq.rfl

theorem augmentedSubmission_successor_heq_existingFirstSuccessor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((augmentedInstalledRenewalAt oldVisit sourceIndex boundary).payload
        ).successor
      (M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  HEq.rfl

theorem augmentedInstalledPayload_carriesCanonicalCertificate
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty
      (SourceNativeSubmittedEffectCertificateAt
        (canonicalAttemptAt oldVisit sourceIndex boundary)) :=
  (augmentedInstalledRenewalAt oldVisit sourceIndex boundary).payload.consumer.down

theorem augmentedInstalledPayload_carriesRootedAuthority
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty
      (SourceNativeObserverConsumerRootedAuthorityAt
        (canonicalSubmissionAt oldVisit sourceIndex boundary)) :=
  ((augmentedInstalledRenewalAt oldVisit sourceIndex boundary).payload
    ).disposition.down

theorem augmentedActualFirstEvent_projectionOutcome_heq_sourceLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((augmentedRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (augmentedRenewalRecognitionAt oldVisit sourceIndex boundary
            ).rootProjection
          ((augmentedRevisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (0 : Nat)))
      ((augmentedRenewalRecognitionAt oldVisit sourceIndex boundary
        ).law.toProjectionLaw.outcomeAt PUnit.unit
          ((augmentedRevisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (0 : Nat))) :=
  (augmentedRenewalRecognitionAt oldVisit sourceIndex boundary
    ).componentOutcome_heq_rootOutcome
      ((augmentedRevisedLivingRootAt oldVisit sourceIndex boundary).emitted
        (0 : Nat))

theorem actualFirstEvent_projectionOutcome_heq_sourceLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((revisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (renewalRecognitionAt oldVisit sourceIndex boundary).rootProjection
          ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (0 : Nat)))
      ((renewalRecognitionAt oldVisit sourceIndex boundary
        ).law.toProjectionLaw.outcomeAt PUnit.unit
          ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (0 : Nat))) :=
  augmentedActualFirstEvent_projectionOutcome_heq_sourceLaw oldVisit
    sourceIndex boundary

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedSubmission_sourceEntry_eq_existingNewOnlyEntry
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedInstalledPayload_carriesRootedAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedActualFirstEvent_projectionOutcome_heq_sourceLaw
