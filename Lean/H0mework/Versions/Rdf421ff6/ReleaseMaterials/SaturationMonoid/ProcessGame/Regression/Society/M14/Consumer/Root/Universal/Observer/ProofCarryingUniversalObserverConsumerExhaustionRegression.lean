import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.SourceNativeObserverConsumerAttemptCompiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Root.Universal.ProofCarryingUniversalSocietyRootGrammarRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Identification.ProofCarryingFullDomainRepairAuthorityObstructionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Consumer.ProofCarryingContributionCapacityCofinalProductiveNovelty

/-!
# M14 universal observer / consumer exhaustion

The exact actual scenario generates world authority independently of whether
the installed grammar is canonical or failed.  The full-capture search keeps
its typed failed-face responsibility but has no actual-write authority.
Arbitrary visible computations remain lawful presentations; source-generated
kernel pairs reject only their attempted authority completeness.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingUniversalObserverConsumerExhaustionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedUniversalSocietyRootGrammarFailure
open M14ProofCarryingUniversalSocietyRootGrammarRegression
open M14FullDomainReachabilityCollision
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14FullDomainRepairAuthorityObstruction
open M14ProofCarryingFullDomainRepairAuthorityObstructionRegression
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14ProofCarryingContributionCapacityCofinalProductiveNovelty

universe uParameter uOutput uDisposition

abbrev UniversalSocietyRootEvent
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ExactTemporalCausalRootEvent
    (UniversalSocietyRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot

/-- Concrete identity consumer used only by the fixed direct certificate. -/
def universalSocietyRootIdentityConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    UniversalSocietyRootEvent oldVisit sourceIndex →
      UniversalSocietyRootEvent oldVisit sourceIndex :=
  id

/-- M14 specialization of the arbitrary-universe full-root readout theorem. -/
theorem universalSocietyRootParameterizedReadout_consumerSafe
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {Parameter : Type uParameter} {Output : Type uOutput}
    {Disposition : Type uDisposition}
    (readout : UniversalSocietyRootEvent oldVisit sourceIndex →
      Parameter → Output)
    (consumer : Output → Disposition) (parameter : Parameter) :
    ConsumerSafe
      (@rootCofaceRead _ _
        (UniversalSocietyRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot)
      (fun event => consumer (readout event parameter)) :=
  rootCofaceParameterizedReadout_consumerSafe readout consumer parameter

/-- The source actual token and living-root evolution are the positive
authority mouth; no readout or desired factorization is supplied. -/
def universalSocietyActualObserverAuthorityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeObserverConsumerAuthorityAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual :=
  sourceNativeObserverConsumerAuthorityAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)

/-- The positive authority subsequently exposes the exact installed trace,
whole ledger and generated next through the existing root theorem. -/
theorem universalSocietyActualObserverAuthority_factorizes
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let authority := universalSocietyActualObserverAuthorityAt oldVisit
      sourceIndex index
    authority.rootEvolution.generated =
        (UniversalSocietyRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
            (universalSocietyVisitAt oldVisit sourceIndex index) ∧
      HEq (authority.rootEvolution.generated.projectionOutcome
          (universalSocietyRecognitionAt oldVisit sourceIndex).rootProjection)
        ((universalSocietyRecognitionAt oldVisit sourceIndex
          ).installedFiberAt
            (universalSocietyVisitAt oldVisit sourceIndex index)) ∧
      HEq ((universalSocietyRecognitionAt oldVisit sourceIndex
          ).wholeLedgerWriteBackAt
            (universalSocietyVisitAt oldVisit sourceIndex index))
        ((UniversalSocietyRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (universalSocietyVisitAt oldVisit sourceIndex index).current) ∧
      authority.rootEvolution.nextCurrent =
        (universalSocietyRecognitionAt oldVisit sourceIndex
          ).generatedNextAt
            (universalSocietyVisitAt oldVisit sourceIndex index) :=
  (universalSocietyActualObserverAuthorityAt oldVisit sourceIndex index
    ).rootLedgerAndNext_factorize

/-- Actual and full-capture consumption use the same root consumer while
retaining independent authority and grammar-disposition axes. -/
def universalSocietyActualObserverExhaustionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceNativeObserverConsumerExhaustionAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .actual
    (universalSocietyRootIdentityConsumer oldVisit sourceIndex)

def universalSocietySearchObserverExhaustionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceNativeObserverConsumerExhaustionAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .fullCaptureSearch
    (universalSocietyRootIdentityConsumer oldVisit sourceIndex)

/-! ## Exact-root submission specialization -/

/-- Identity visibility on the complete root-event carrier.  Its authority K
is still generated by the generic source adapter, not stored here. -/
def universalSocietyIdentityRootObserverAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeSocietyObserverAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (UniversalSocietyRootEvent oldVisit sourceIndex) where
  forget := id

def universalSocietyRootAuthorityKReadoutAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    OccurrenceReadout (UniversalSocietyRootEvent oldVisit sourceIndex)
      (SourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)) where
  read := sourceNativeObserverRootAuthorityKAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)

/-- Arbitrary body with no claim, certificate, branch or result field. -/
def universalSocietyRootAuthorityAttemptAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :
    SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      (UniversalSocietyRootEvent oldVisit sourceIndex)
      (SourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex))
      (SourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)) where
  observer := universalSocietyIdentityRootObserverAt oldVisit sourceIndex
  readout := universalSocietyRootAuthorityKReadoutAt oldVisit sourceIndex
  consumer := id

def universalSocietyRootAuthorityAttemptFactorizationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :
    let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
      index scenario
    ReadoutFactorization attempt.observer.toAuthorityObserver
      attempt.consumedReadout where
  visibleReadout := sourceNativeObserverRootAuthorityKAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
  factorizes := fun _event => rfl

def universalSocietyRootAuthorityAttemptCompleteAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :
    let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
      index scenario
    AuthorityCompleteReadoutAt attempt.observer.toAuthorityObserver
      attempt.consumedReadout where
  decodeAuthority := id
  readsActualAuthority := fun _event => rfl

/-- The certificate is installed into a later source submission occurrence;
it is never passed to the compiler mouth. -/
def universalSocietyRootAuthorityAttemptCertificateAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :
    let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
      index scenario
    SourceNativeSubmittedEffectCertificateAt attempt where
  factorization :=
    universalSocietyRootAuthorityAttemptFactorizationAt oldVisit sourceIndex
      index scenario
  complete :=
    universalSocietyRootAuthorityAttemptCompleteAt oldVisit sourceIndex index
      scenario

def universalSocietyCertifiedRootAuthorityProgramAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :=
  certifiedAuthoritySubmissionProgramAt
    (universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex index
      scenario)
    (universalSocietyRootAuthorityAttemptCertificateAt oldVisit sourceIndex
      index scenario)

def universalSocietyCompiledRootAuthorityAttemptAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario) :=
  compileSourceNativeObserverConsumerSubmissionAt
    (universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
      index scenario).generate

/-- Universe-polymorphic maximum over every sealed submission occurrence.
Neither certificate nor result branch appears at the compiler mouth. -/
theorem universalSocietyEverySealedSubmission_rooted_iff
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uParameter} {Output : Type uOutput}
    {ClaimedEffect : Type uDisposition}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    (compileSourceNativeObserverConsumerSubmissionAt generated
        ).useDisposition.IsRooted ↔
      generated.CarriesCertifiedAuthority ∧
        scenario = (universalSocietyRecognitionAt oldVisit sourceIndex
          ).installedActualScenarioAt
            (universalSocietyVisitAt oldVisit sourceIndex index) :=
  compile_isRooted_iff_certifiedAndInstalledActual generated

theorem universalSocietyEveryCertifiedSubmission_rooted_iff_installedActual
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uParameter} {Output : Type uOutput}
    {ClaimedEffect : Type uDisposition}
    (attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect)
    (certificate : SourceNativeSubmittedEffectCertificateAt attempt) :
    let program :=
      certifiedAuthoritySubmissionProgramAt attempt certificate
    (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition.IsRooted ↔
      scenario = (universalSocietyRecognitionAt oldVisit sourceIndex
        ).installedActualScenarioAt
          (universalSocietyVisitAt oldVisit sourceIndex index) :=
  compile_certified_isRooted_iff_installedActual attempt certificate

/-- The concrete identity consumer's effect really decodes root K at every
event. -/
theorem universalSocietyRootAuthorityConsumerEffect_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : PostSettlementSocietyScenario)
    (event : UniversalSocietyRootEvent oldVisit sourceIndex) :
    (universalSocietyRootAuthorityAttemptCompleteAt oldVisit sourceIndex index
      scenario).decodeAuthority
        ((universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex index
          scenario).consumer
          ((universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex index
            scenario).readout.read event)) =
      sourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex) event :=
  rfl

theorem universalSocietyActualRawAttempt_isRooted
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (universalSocietyCompiledRootAuthorityAttemptAt oldVisit sourceIndex index
      .actual).useDisposition.IsRooted :=
  (universalSocietyEveryCertifiedSubmission_rooted_iff_installedActual oldVisit
    sourceIndex index .actual
    (universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex index .actual)
    (universalSocietyRootAuthorityAttemptCertificateAt oldVisit sourceIndex
      index .actual)).2
        (universalSocietyInstalledActualScenario_eq oldVisit sourceIndex
          index).symm

theorem universalSocietyActualRawAttempt_rootedAuthority_nonempty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
      (SourceNativeObserverConsumerRootedAuthorityAt
        (universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
          index .actual).generate) := by
  let compiled := universalSocietyCompiledRootAuthorityAttemptAt oldVisit
    sourceIndex index .actual
  have rooted : compiled.useDisposition.IsRooted :=
    universalSocietyActualRawAttempt_isRooted oldVisit sourceIndex index
  generalize dispositionExact : compiled.useDisposition = disposition at rooted
  cases disposition with
  | presentation =>
      simp [SourceNativeObserverConsumerUseDispositionAt.IsRooted]
        at rooted
  | rooted authority => exact ⟨authority⟩
  | rejected rejection =>
      simp [SourceNativeObserverConsumerUseDispositionAt.IsRooted]
        at rooted

theorem universalSocietySearchRawAttempt_isRejected
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let program := universalSocietyCertifiedRootAuthorityProgramAt
      oldVisit sourceIndex index .fullCaptureSearch
    ∃ rejection : SourceNativeObserverConsumerRejectionAt
        program.generate,
      (universalSocietyCompiledRootAuthorityAttemptAt oldVisit sourceIndex
        index .fullCaptureSearch).useDisposition = .rejected rejection := by
  let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
    index .fullCaptureSearch
  let certificate := universalSocietyRootAuthorityAttemptCertificateAt oldVisit
    sourceIndex index .fullCaptureSearch
  let program := universalSocietyCertifiedRootAuthorityProgramAt oldVisit
    sourceIndex index .fullCaptureSearch
  let identityDisposition :=
    @sourceNativeSearchIdentityDispositionAt
      (JointSettlementNAt oldVisit) (PostSettlementRenewalVAt oldVisit)
      (UniversalSocietyRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.source
      (universalSocietyVisitAt oldVisit sourceIndex index).current
      ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
        (universalSocietyVisitAt oldVisit sourceIndex index).current)
  exact
    ⟨.nonActual certificate rfl fullCaptureSearch_ne_actual
        identityDisposition,
      rfl⟩

theorem universalSocietyPresentationSubmission_isPresentation
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
      index .actual
    let program := presentationSubmissionProgramAt attempt
    (compileSourceNativeObserverConsumerSubmissionAt program.generate
      ).useDisposition = .presentation :=
  compile_presentation_exact _

theorem universalSocietyUncertifiedSubmission_isRejected
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
      index .actual
    let program := uncertifiedAuthoritySubmissionProgramAt attempt
    ∃ rejection : SourceNativeObserverConsumerRejectionAt
        program.generate,
      (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition = .rejected rejection :=
  compile_uncertified_isRejected _

/-! ## Actual same-visible / different-K source challenge -/

def universalSocietyConstantRootObserverAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeSocietyObserverAt
      (universalSocietyRecognitionAt oldVisit sourceIndex) Unit where
  forget := fun _event => ()

def universalSocietyConstantObserverAttemptAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual
      Unit Unit Unit where
  observer := universalSocietyConstantRootObserverAt oldVisit sourceIndex
  readout := ⟨fun _event => ()⟩
  consumer := id

def universalSocietyExactObserverEventAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    UniversalSocietyRootEvent oldVisit sourceIndex :=
  ⟨universalSocietyVisitAt oldVisit sourceIndex index,
    (universalSocietyRecognitionAt oldVisit sourceIndex).exactEventAt
      (universalSocietyVisitAt oldVisit sourceIndex index)⟩

theorem universalSocietyExactObserverEvents_ne
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietyExactObserverEventAt oldVisit sourceIndex index ≠
      universalSocietyExactObserverEventAt oldVisit sourceIndex (index + 1) := by
  intro sameEvent
  have sameCurrent := congrArg (fun event => event.1.current) sameEvent
  simp [universalSocietyExactObserverEventAt, universalSocietyVisitAt]
    at sameCurrent
  have impossible := Nat.add_left_cancel sameCurrent
  exact Nat.ne_of_lt (Nat.lt_succ_self (index + 1 + 1)) impossible

theorem universalSocietyExactObserverAuthorityK_ne
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    sourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyExactObserverEventAt oldVisit sourceIndex index) ≠
      sourceNativeObserverRootAuthorityKAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyExactObserverEventAt oldVisit sourceIndex
          (index + 1)) := by
  intro sameAuthority
  have sameCurrent := congrArg (fun authority => authority.visit.current)
    sameAuthority
  simp [sourceNativeObserverRootAuthorityKAt,
    universalSocietyExactObserverEventAt, universalSocietyVisitAt]
    at sameCurrent
  have impossible := Nat.add_left_cancel sameCurrent
  exact Nat.ne_of_lt (Nat.lt_succ_self (index + 1 + 1)) impossible

def universalSocietyConstantObserverKernelPairAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let attempt := universalSocietyConstantObserverAttemptAt oldVisit
      sourceIndex index
    AuthorityKernelPair attempt.observer.toAuthorityObserver where
  left := universalSocietyExactObserverEventAt oldVisit sourceIndex index
  right := universalSocietyExactObserverEventAt oldVisit sourceIndex
    (index + 1)
  occurrence_ne := universalSocietyExactObserverEvents_ne oldVisit sourceIndex
    index
  visible_eq := rfl
  authority_ne := universalSocietyExactObserverAuthorityK_ne oldVisit
    sourceIndex index

def universalSocietyConstantObserverFactorizationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let attempt := universalSocietyConstantObserverAttemptAt oldVisit
      sourceIndex index
    ReadoutFactorization attempt.observer.toAuthorityObserver
      attempt.consumedReadout where
  visibleReadout := id
  factorizes := fun _event => rfl

def universalSocietyConstantObserverKernelChallengeAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let attempt := universalSocietyConstantObserverAttemptAt oldVisit
      sourceIndex index
    SourceNativeSubmittedKernelChallengeAt attempt where
  factorization := universalSocietyConstantObserverFactorizationAt oldVisit
    sourceIndex index
  kernelPair := universalSocietyConstantObserverKernelPairAt oldVisit
    sourceIndex index

def universalSocietyChallengedConstantObserverProgramAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  kernelChallengedAuthoritySubmissionProgramAt
    (universalSocietyConstantObserverAttemptAt oldVisit sourceIndex index)
    (universalSocietyConstantObserverKernelChallengeAt oldVisit sourceIndex
      index)

def universalSocietyCompiledChallengedConstantObserverAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  compileSourceNativeObserverConsumerSubmissionAt
    (universalSocietyChallengedConstantObserverProgramAt oldVisit
      sourceIndex index).generate

/-- A real actual-world kernel challenge is rejected as hidden while the
compiled world axis remains actual and the installed grammar remains live. -/
theorem universalSocietyActualKernelChallenge_isHiddenRejected
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let program := universalSocietyChallengedConstantObserverProgramAt
      oldVisit sourceIndex index
    ∃ rejection : SourceNativeObserverConsumerRejectionAt
        program.generate,
      (universalSocietyCompiledChallengedConstantObserverAt oldVisit
        sourceIndex index).useDisposition = .rejected rejection :=
  compile_challenged_isHiddenRejected _ _

/-- The actual authority carrier is nonempty exactly at the installed actual
scenario. -/
theorem universalSocietyActualAuthority_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
      (SourceNativeObserverConsumerAuthorityAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) .actual) ∧
      PostSettlementSocietyScenario.actual =
        (universalSocietyRecognitionAt oldVisit sourceIndex
          ).installedActualScenarioAt
            (universalSocietyVisitAt oldVisit sourceIndex index) := by
  let authority := universalSocietyActualObserverAuthorityAt oldVisit
    sourceIndex index
  exact
    ⟨⟨authority⟩,
      (SourceNativeObserverConsumerAuthorityAt.nonempty_iff_installedActualScenario
        (recognition := universalSocietyRecognitionAt oldVisit sourceIndex)
        (visit := universalSocietyVisitAt oldVisit sourceIndex index)
        (scenario := PostSettlementSocietyScenario.actual)).1 ⟨authority⟩⟩

/-- The search is a lawful full-root presentation with a genuine failed-face
disposition, but its actual authority carrier is empty. -/
theorem universalSocietySearchAuthority_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (SourceNativeObserverConsumerAuthorityAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index)
        .fullCaptureSearch) :=
  ⟨fun authority =>
    (sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index).searchNoActualWrite.false authority.scenarioAuthority⟩

/-- The existing failure is the typed rejection: all residual responsibility
stays live while search applies only identity to the actual write-back. -/
theorem universalSocietySearchTypedRejection
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let failure := sourceGeneratedUniversalSocietyRootGrammarFailureAt
      oldVisit sourceIndex index
    Nonempty (PeriodicActualServiceExitAt
        (show Nat from
          (universalSocietyVisitAt oldVisit sourceIndex index).current)) ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          failure.residualBearer) ∧
      Nonempty
        (PostSettlementFullCaptureAuditDispositionAt oldVisit sourceIndex
          ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
            (universalSocietyVisitAt oldVisit sourceIndex index).current)
          .fullCaptureSearch .bearerRoleIndependentContinuation
          failure.residualBearer failure.rootConsumer) ∧
      Nonempty
        (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
          (index + 1 + 1)
          (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex
            index).exactEvent failure.residualBearer) ∧
      IsEmpty
        (SourceNativeScenarioActualWriteAuthorityAt
          (postSettlementSocietyVocabulary oldVisit sourceIndex)
          .fullCaptureSearch) ∧
      failure.auditDisposition.applyToActualWriteBack
          ((universalSocietyActualGrammarAt oldVisit sourceIndex index
            ).wholeLedgerWriteBack) =
        (universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index).exactEvent =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).exactEvent ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack ∧
      (universalSocietyActualGrammarAt oldVisit sourceIndex index).generatedNext =
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).generatedNext := by
  let failure := sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit
    sourceIndex index
  exact
    ⟨⟨failure.residualBearer⟩,
      ⟨failure.sourceOwnedResidual⟩,
      ⟨failure.rootConsumer⟩,
      ⟨failure.auditDisposition⟩,
      ⟨failure.externalLiability⟩,
      failure.searchNoActualWrite,
      failure.auditPreservesActualWriteBack,
      failure.sameRootLedgerAndNext.1,
      failure.sameRootLedgerAndNext.2.1,
      failure.sameRootLedgerAndNext.2.2⟩

/-! ## Arbitrary visible presentation, coarse rejection and refined positive -/

/-- Any output computed on the existing coarse visible image remains a
lawful presentation. -/
theorem fullDomain_visiblePresentation_nonempty
    (depth : Nat) {Output : Type uOutput}
    (visibleReadout : FullDomainReachabilityObservation → Output) :
    Nonempty
      (ReadoutFactorization (fullDomainRepairObserverAt depth)
        (OccurrenceReadout.ofVisible (fullDomainRepairObserverAt depth)
          visibleReadout)) :=
  ReadoutFactorization.visibleComputation_nonempty _ visibleReadout

/-- At every output universe, coarse factorization cannot also decode actual
repair authority. -/
theorem fullDomain_factoredOutput_authorityComplete_isEmpty
    (depth : Nat) {Output : Type uOutput}
    (readout : OccurrenceReadout (RepairFailureOriginAt depth) Output)
    (factorization : ReadoutFactorization
      (fullDomainRepairObserverAt depth) readout) :
    IsEmpty (AuthorityCompleteReadoutAt
      (fullDomainRepairObserverAt depth) readout) :=
  ⟨fun complete =>
    (fullDomain_factoredReadout_not_authorityComplete depth readout
      factorization) ⟨complete⟩⟩

/-- Cofinal same-normal-form/different-K paid replays remain an independent
source-generated kernel witness, not a fixed repair-only example. -/
theorem universalSocietyCofinalKernelConsumed
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityCofinalProductiveNoveltyCertificateAt
      oldVisit sourceIndex :=
  proofCarryingContributionCapacityCofinalProductiveNovelty oldVisit
    sourceIndex

/-! ## Whole direct certificate -/

structure ProofCarryingUniversalObserverConsumerExhaustionCertificate : Prop where
  everyRawActualAttemptRooted : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      (universalSocietyCompiledRootAuthorityAttemptAt oldVisit sourceIndex
        index .actual).useDisposition.IsRooted
  everyRawSearchAttemptRejected : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      let program := universalSocietyCertifiedRootAuthorityProgramAt
        oldVisit sourceIndex index .fullCaptureSearch
      ∃ rejection : SourceNativeObserverConsumerRejectionAt
          program.generate,
        (universalSocietyCompiledRootAuthorityAttemptAt oldVisit sourceIndex
          index .fullCaptureSearch).useDisposition = .rejected rejection
  everyPresentationSubmissionExact : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
        index .actual
      let program := presentationSubmissionProgramAt attempt
      (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition = .presentation
  everyUncertifiedSubmissionRejected : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      let attempt := universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
        index .actual
      let program := uncertifiedAuthoritySubmissionProgramAt attempt
      ∃ rejection : SourceNativeObserverConsumerRejectionAt
          program.generate,
        (compileSourceNativeObserverConsumerSubmissionAt program.generate
          ).useDisposition = .rejected rejection
  everyActualKernelChallengeHiddenRejected : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      let program := universalSocietyChallengedConstantObserverProgramAt
        oldVisit sourceIndex index
      ∃ rejection : SourceNativeObserverConsumerRejectionAt
          program.generate,
        (universalSocietyCompiledChallengedConstantObserverAt oldVisit
          sourceIndex index).useDisposition = .rejected rejection
  everyRawIdentityConsumerEffectExact : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
    ∀ scenario : PostSettlementSocietyScenario,
    ∀ event : UniversalSocietyRootEvent oldVisit sourceIndex,
      (universalSocietyRootAuthorityAttemptCompleteAt oldVisit sourceIndex
        index scenario).decodeAuthority
          ((universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex index
            scenario).consumer
            ((universalSocietyRootAuthorityAttemptAt oldVisit sourceIndex
              index scenario).readout.read event)) =
        sourceNativeObserverRootAuthorityKAt
          (universalSocietyRecognitionAt oldVisit sourceIndex) event
  everyActualTwoAxisExhaustion : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      Nonempty
        (SourceNativeObserverConsumerExhaustionAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index) .actual
          (universalSocietyRootIdentityConsumer oldVisit sourceIndex))
  everySearchTwoAxisExhaustion : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      Nonempty
        (SourceNativeObserverConsumerExhaustionAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index)
          .fullCaptureSearch
          (universalSocietyRootIdentityConsumer oldVisit sourceIndex))
  everyActualGrammarCanonical : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      universalSocietyActualCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.canonical
          (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index)
  everySearchGrammarFailed : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.failed
          (universalSocietyFullCaptureSearchFailureAuditAt oldVisit
            sourceIndex index)
  everyActualAuthority : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (SourceNativeObserverConsumerAuthorityAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) .actual)
  everyActualRootFactorization : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      let authority := universalSocietyActualObserverAuthorityAt oldVisit
        sourceIndex index
      authority.rootEvolution.generated =
          (UniversalSocietyRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
              (universalSocietyVisitAt oldVisit sourceIndex index) ∧
        HEq (authority.rootEvolution.generated.projectionOutcome
            (universalSocietyRecognitionAt oldVisit sourceIndex).rootProjection)
          ((universalSocietyRecognitionAt oldVisit sourceIndex
            ).installedFiberAt
              (universalSocietyVisitAt oldVisit sourceIndex index)) ∧
        HEq ((universalSocietyRecognitionAt oldVisit sourceIndex
            ).wholeLedgerWriteBackAt
              (universalSocietyVisitAt oldVisit sourceIndex index))
          ((UniversalSocietyRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
              (universalSocietyVisitAt oldVisit sourceIndex index).current) ∧
        authority.rootEvolution.nextCurrent =
          (universalSocietyRecognitionAt oldVisit sourceIndex
            ).generatedNextAt
              (universalSocietyVisitAt oldVisit sourceIndex index)
  everySearchAuthorityEmpty : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      IsEmpty
        (SourceNativeObserverConsumerAuthorityAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index)
          .fullCaptureSearch)
  everySearchTypedRejection : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
      Nonempty
        (SourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit
          sourceIndex index)
  everyThirdAuthorityEmpty : ∀ oldVisit : OldVisit,
    ∀ sourceIndex index : Nat,
    ∀ scenario : PostSettlementSocietyScenario,
      IsEmpty
        (ExactUnaccountedObserverAuthorityAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index) scenario)
  everyCoarseAuthorityFactorizationEmpty : ∀ depth : Nat,
    IsEmpty (AuthorityFactorization (fullDomainRepairObserverAt depth))
  everyCoarseIdentityPresentation : ∀ depth : Nat,
    Nonempty
      (ReadoutFactorization (fullDomainRepairObserverAt depth)
        (OccurrenceReadout.ofVisible (fullDomainRepairObserverAt depth) id))
  everyRefinedPositive : ∀ depth : Nat,
    Nonempty (AuthorityFactorization
      (failureKindRefinedFullDomainRepairObserverAt depth))
  everyCofinalKernel : ∀ oldVisit : OldVisit, ∀ sourceIndex : Nat,
    ProofCarryingContributionCapacityCofinalProductiveNoveltyCertificateAt
      oldVisit sourceIndex
  universalGrammar : ProofCarryingUniversalSocietyRootGrammarCertificate

theorem proofCarryingUniversalObserverConsumerExhaustionDirectConsumer :
    ProofCarryingUniversalObserverConsumerExhaustionCertificate where
  everyRawActualAttemptRooted := universalSocietyActualRawAttempt_isRooted
  everyRawSearchAttemptRejected :=
    universalSocietySearchRawAttempt_isRejected
  everyPresentationSubmissionExact :=
    universalSocietyPresentationSubmission_isPresentation
  everyUncertifiedSubmissionRejected :=
    universalSocietyUncertifiedSubmission_isRejected
  everyActualKernelChallengeHiddenRejected :=
    universalSocietyActualKernelChallenge_isHiddenRejected
  everyRawIdentityConsumerEffectExact :=
    universalSocietyRootAuthorityConsumerEffect_exact
  everyActualTwoAxisExhaustion := fun oldVisit sourceIndex index =>
    ⟨universalSocietyActualObserverExhaustionAt oldVisit sourceIndex index⟩
  everySearchTwoAxisExhaustion := fun oldVisit sourceIndex index =>
    ⟨universalSocietySearchObserverExhaustionAt oldVisit sourceIndex index⟩
  everyActualGrammarCanonical := universalSocietyActualCompiler_isCanonical
  everySearchGrammarFailed :=
    universalSocietyFullCaptureSearchCompiler_isFailed
  everyActualAuthority := fun oldVisit sourceIndex index =>
    (universalSocietyActualAuthority_exact oldVisit sourceIndex index).1
  everyActualRootFactorization :=
    universalSocietyActualObserverAuthority_factorizes
  everySearchAuthorityEmpty := universalSocietySearchAuthority_isEmpty
  everySearchTypedRejection := fun oldVisit sourceIndex index =>
    ⟨sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index⟩
  everyThirdAuthorityEmpty := fun oldVisit sourceIndex index scenario =>
    exactUnaccountedObserverAuthority_isEmpty
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
  everyCoarseAuthorityFactorizationEmpty := fun depth =>
    ⟨fun factorization =>
      (fullDomainRepairAuthorityNoGos depth).1 ⟨factorization⟩⟩
  everyCoarseIdentityPresentation := fun depth =>
    fullDomain_visiblePresentation_nonempty depth id
  everyRefinedPositive := fun depth =>
    (failureKindRefinementControls depth).2.2.2
  everyCofinalKernel := universalSocietyCofinalKernelConsumed
  universalGrammar := proofCarryingUniversalSocietyRootGrammarDirectConsumer

namespace ProofCarryingUniversalObserverConsumerExhaustionCertificate

/-- The fixed M14 sink exports the universe-polymorphic maximum for every
program-generated submission occurrence. -/
theorem everySealedSubmission_rooted_iff
    (_certificate : ProofCarryingUniversalObserverConsumerExhaustionCertificate)
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uParameter} {Output : Type uOutput}
    {ClaimedEffect : Type uDisposition}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    (compileSourceNativeObserverConsumerSubmissionAt generated
        ).useDisposition.IsRooted ↔
      generated.CarriesCertifiedAuthority ∧
        scenario = (universalSocietyRecognitionAt oldVisit sourceIndex
          ).installedActualScenarioAt
            (universalSocietyVisitAt oldVisit sourceIndex index) := by
  cases _certificate
  exact universalSocietyEverySealedSubmission_rooted_iff
    oldVisit sourceIndex index scenario generated

/-- Every fixed program-generated occurrence has no fourth disposition. -/
theorem everySubmission_exhaustive
    (_certificate : ProofCarryingUniversalObserverConsumerExhaustionCertificate)
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uParameter} {Output : Type uOutput}
    {ClaimedEffect : Type uDisposition}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    let compiled := compileSourceNativeObserverConsumerSubmissionAt generated
    (compiled.useDisposition = .presentation) ∨
      (∃ authority : SourceNativeObserverConsumerRootedAuthorityAt generated,
        compiled.useDisposition = .rooted authority) ∨
      (∃ rejection : SourceNativeObserverConsumerRejectionAt generated,
        compiled.useDisposition = .rejected rejection) := by
  cases _certificate
  exact compiledSubmission_exhaustive generated

theorem sameExactSubmission_noSecondDisposition
    (_certificate : ProofCarryingUniversalObserverConsumerExhaustionCertificate)
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uParameter} {Output : Type uOutput}
    {ClaimedEffect : Type uDisposition}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (left right : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    (compileSourceNativeObserverConsumerSubmissionAt left).useDisposition =
      (compileSourceNativeObserverConsumerSubmissionAt right).useDisposition := by
  cases _certificate
  exact UniversalRootGrammar.sameExactSubmission_noSecondDisposition
    left right

end ProofCarryingUniversalObserverConsumerExhaustionCertificate

end
end M14ProofCarryingUniversalObserverConsumerExhaustionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.universalSocietyActualObserverAuthority_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.universalSocietyEverySealedSubmission_rooted_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.ProofCarryingUniversalObserverConsumerExhaustionCertificate.everySubmission_exhaustive
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.ProofCarryingUniversalObserverConsumerExhaustionCertificate.sameExactSubmission_noSecondDisposition
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.universalSocietySearchTypedRejection
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.fullDomain_factoredOutput_authorityComplete_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalObserverConsumerExhaustionRegression.proofCarryingUniversalObserverConsumerExhaustionDirectConsumer
