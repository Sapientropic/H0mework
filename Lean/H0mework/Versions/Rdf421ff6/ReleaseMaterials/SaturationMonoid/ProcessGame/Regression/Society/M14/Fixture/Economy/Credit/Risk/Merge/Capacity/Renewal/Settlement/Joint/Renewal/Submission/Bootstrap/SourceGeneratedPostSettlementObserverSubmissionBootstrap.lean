import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Root.Universal.Observer.ProofCarryingUniversalObserverConsumerExhaustionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Failure.Producer.SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure

/-!
# Post-settlement observer-submission U8 bootstrap

One cofinal novelty token fixes its right paid replay.  The replay's exact
external Payment fixes the literal M9 joint-root visit, rooted failure and
canonical minimal coface.  Independently, the same boundary fixes the
canonical actual observer submission.  The local process seed contains only
the proof that this exact submission occurrence was generated; its consumer
and disposition are the submitted certificate and the compiler's rooted-use
fact.  No revised network, row, successor or future is admitted here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression

def noveltyAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
    sourceIndex boundary

def rootedBridgeAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    (noveltyAt oldVisit sourceIndex boundary)

def rightReplayAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (rootedBridgeAt oldVisit sourceIndex boundary).rightReplay

def rightCurrentAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Nat :=
  (rightReplayAt oldVisit sourceIndex boundary).2.current

def oldRootVisitAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RootVisit jointRoot.toAuthoritativeRoot.toRoot :=
  (rootedBridgeAt oldVisit sourceIndex boundary).rightRootVisit

def rootedFailureAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (rootedBridgeAt oldVisit sourceIndex boundary).rightRootedFailure

def canonicalCofaceAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (rootedBridgeAt oldVisit sourceIndex boundary).rightMinimalCoface

theorem rightPaymentRootOccurrence_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
      ).paymentOccurrence.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  (rootedBridgeAt oldVisit sourceIndex boundary
    ).rightPaymentRootOccurrence_exact

theorem rootedOccurrence_isRightPaymentOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((rootedFailureAt oldVisit sourceIndex boundary).oldBoundaryEvolution
      ).occurrence =
      (((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence).rootOccurrence.occurrence :=
  (rootedBridgeAt oldVisit sourceIndex boundary
    ).rightRootedOccurrence_isPaymentOccurrence

theorem canonicalCoface_isGeneratedFromRightPaymentRootedFailure
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    canonicalCofaceAt oldVisit sourceIndex boundary =
      root_obstruction_generates_minimal_coface
        (rootedFailureAt oldVisit sourceIndex boundary) :=
  rfl

/-! ## Canonical actual submission fixed by the same boundary -/

/-- `universalSocietyVisitAt` already advances by two renewal steps.  Using
the raw novelty boundary therefore lands on the right replay's literal
`boundary + 2` post-settlement current; adding two here would silently select
a later sibling event. -/
def submissionIndexAt (_oldVisit : OldVisit) (_sourceIndex boundary : Nat) :
    Nat :=
  boundary

theorem canonicalSubmissionCurrent_eq_rightReplayCurrent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (show Nat from
      (universalSocietyVisitAt oldVisit sourceIndex
        (submissionIndexAt oldVisit sourceIndex boundary)).current) =
      rightCurrentAt oldVisit sourceIndex boundary := by
  rfl

def canonicalAttemptAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
    (submissionIndexAt oldVisit sourceIndex boundary) .actual

def canonicalCertificateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  universalSocietyRootAuthorityAttemptCertificateAt oldVisit sourceIndex
    (submissionIndexAt oldVisit sourceIndex boundary) .actual

def canonicalProgramAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
    (submissionIndexAt oldVisit sourceIndex boundary) .actual

theorem canonicalSubmissionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceGeneratedObserverConsumerSubmissionAt
      (canonicalProgramAt oldVisit sourceIndex boundary)
      (.authorityCertified
        (canonicalCertificateAt oldVisit sourceIndex boundary)) :=
  (canonicalProgramAt oldVisit sourceIndex boundary).generate

theorem canonicalSubmission_isRooted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (compileSourceNativeObserverConsumerSubmissionAt
      (canonicalSubmissionAt oldVisit sourceIndex boundary)
      ).useDisposition.IsRooted :=
  universalSocietyActualRawAttempt_isRooted oldVisit sourceIndex
    (submissionIndexAt oldVisit sourceIndex boundary)

/-- The lower submission program consumes the literal post-settlement event
already carried by the right replay.  The external Payment occurrence is then
read from that replay's source-generated liability bridge; current equality
alone is not used as a transporter. -/
theorem canonicalSubmission_exactEvent_eq_rightReplayPostRootEvent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (canonicalSubmissionAt oldVisit sourceIndex boundary).exactEvent =
      (rightReplayAt oldVisit sourceIndex boundary).2.rootEvent :=
  rfl

theorem canonicalSubmission_sourceOccurrence_eq_rightReplayPostRootOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (canonicalSubmissionAt oldVisit sourceIndex boundary).sourceOccurrence =
      ⟨universalSocietyVisitAt oldVisit sourceIndex boundary,
        (rightReplayAt oldVisit sourceIndex boundary).2.rootEvent⟩ :=
  rfl

/-! ## Proof-only local source seed / consumer / disposition -/

abbrev LocalSource := Unit

/-- Exact installed 16-point Society trace at the right replay's
post-settlement current.  The renewal seed below is witnessed in this
existing occurrence; no dummy or second `RootedAccountedUnfolding` is built. -/
def localSocietyOccurrenceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  (UniversalSocietyRootAt oldVisit sourceIndex).emitted
    (universalSocietyVisitAt oldVisit sourceIndex
      (submissionIndexAt oldVisit sourceIndex boundary)).current

abbrev LocalState (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  PostSettlementSocietyPointAt oldVisit sourceIndex
    (localSocietyOccurrenceAt oldVisit sourceIndex boundary)

inductive SubmissionMaterialKind
  | authorityCertified

abbrev LocalSeed := SubmissionMaterialKind

def localOccurrenceOf (_oldVisit : OldVisit) (_sourceIndex _boundary : Nat)
    (_source : LocalSource) :
    RootedAccountedUnfolding
      (LocalState _oldVisit _sourceIndex _boundary) :=
  postSettlementSocietyTraceAt _oldVisit _sourceIndex
    (localSocietyOccurrenceAt _oldVisit _sourceIndex _boundary)

def localGame (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SaturationMonoid.ProcessGame
      (localOccurrenceOf oldVisit sourceIndex boundary) :=
  ⟨()⟩

def LocalSeedAt (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_source : LocalSource)
    (_state : LocalState oldVisit sourceIndex boundary)
    (_seed : LocalSeed) : Prop :=
  _seed = .authorityCertified ∧
    _state.scenario = .actual ∧
    _state.face = .ledger

def localSourceSeed (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceSeed (localOccurrenceOf oldVisit sourceIndex boundary) LocalSeed
      (LocalSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source := by
  refine ⟨.authorityCertified, ?_⟩
  let occurrence := localOccurrenceOf oldVisit sourceIndex boundary
    (localGame oldVisit sourceIndex boundary).source
  exact ⟨occurrence.root, occurrence.root_mem_trace, rfl, rfl, rfl⟩

abbrev LocalConsumerAt (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_seed : SourceSeed
      (localOccurrenceOf oldVisit sourceIndex boundary) LocalSeed
      (LocalSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source) :=
  PLift (Nonempty
    (SourceNativeSubmittedEffectCertificateAt
      (canonicalAttemptAt oldVisit sourceIndex boundary)))

abbrev LocalDispositionAt (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_seed : SourceSeed
      (localOccurrenceOf oldVisit sourceIndex boundary) LocalSeed
      (LocalSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source) :=
  PLift (Nonempty
    (SourceNativeObserverConsumerRootedAuthorityAt
      (canonicalSubmissionAt oldVisit sourceIndex boundary)))

def localConsumer (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    LocalConsumerAt oldVisit sourceIndex boundary
      (localSourceSeed oldVisit sourceIndex boundary) :=
  ⟨⟨canonicalCertificateAt oldVisit sourceIndex boundary⟩⟩

def localDisposition (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    LocalDispositionAt oldVisit sourceIndex boundary
      (localSourceSeed oldVisit sourceIndex boundary) :=
  ⟨universalSocietyActualRawAttempt_rootedAuthority_nonempty oldVisit
    sourceIndex (submissionIndexAt oldVisit sourceIndex boundary)⟩

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rootedOccurrence_isRightPaymentOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.canonicalSubmissionCurrent_eq_rightReplayCurrent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.canonicalSubmission_exactEvent_eq_rightReplayPostRootEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.canonicalSubmission_sourceOccurrence_eq_rightReplayPostRootOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.canonicalSubmission_isRooted
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.localSourceSeed
