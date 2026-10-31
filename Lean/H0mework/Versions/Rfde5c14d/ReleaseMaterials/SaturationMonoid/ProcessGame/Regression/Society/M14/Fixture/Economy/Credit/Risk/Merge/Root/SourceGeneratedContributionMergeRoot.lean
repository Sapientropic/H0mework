import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Compiler.SourceGeneratedContributionMergeRestructuring

/-!
# M14 source-generated contribution-merge root

This module installs the already complete contribution-merge source,
restructuring compiler and lifecycle readout in one living root.  The root's
initial occurrence still carries the conservative A/B/obstruction ledger.
Only its first whole-ledger compiler image generates the two-row merged
target.

The root inventory exposes that exact whole-ledger image with pointwise
lifecycle obligations, plus separately authorized inquiry, answer and
consumer faces.  No sequential-action program, action receipt, runtime,
capacity theory, external registry or second authority compiler is
introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeLifecycle
open M14SourceGeneratedContributionMergeRestructuring

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure
      M14SourceGeneratedLossAllocationWorld.OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus M14SourceGeneratedLossAllocationWorld.OldN}
    {oldTheory : TheoryState M14SourceGeneratedLossAllocationWorld.OldN}
    {support : M14SourceGeneratedLossAllocationWorld.OldN.Support}
    {obstruction :
      M14SourceGeneratedLossAllocationWorld.OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

/-! ## Root-semantic answered inquiry surface -/

/-- The inquiry row follows obstruction continuity.  It is deliberately not
the merged contribution row: inquiry/search and the contribution action share
one root without borrowing each other's row authority. -/
def contributionMergeInquiryEntryAt
    (rooted : RootedFailure) :
    (current : (TargetV rooted).Current) →
      OpenResponsibilityAt (TargetN rooted)
        (contributionMergeSupportAt rooted current)
  | 0 => initialObstruction rooted
  | _ + 1 => mergedObstructionEntry rooted

@[simp] theorem contributionMergeInquiryEntryAt_zero
    (rooted : RootedFailure) :
    contributionMergeInquiryEntryAt rooted 0 = initialObstruction rooted :=
  rfl

@[simp] theorem contributionMergeInquiryEntryAt_succ
    (rooted : RootedFailure) (current : Nat) :
    contributionMergeInquiryEntryAt rooted (current + 1) =
      mergedObstructionEntry rooted :=
  rfl

def contributionMergeU7
    (rooted : RootedFailure) : U7ProducerCalculus (TargetN rooted) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def contributionMergeU7Source
    (rooted : RootedFailure) :
    U7ActualSuccessorSource (TargetN rooted) (contributionMergeU7 rooted) where
  EventAt := SourceGeneratedU7DemandAt (contributionMergeU7 rooted)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ =>
    contributionMergeDefaultEntryAt rooted support

/-- Minimal total calculus needed by the already-answered inquiry token.  It
adds no theory-audit branch; every hypothetical obstruction is redirected on
the exact default row supplied by the conservative representation face. -/
def contributionMergeCalculus
    (rooted : RootedFailure) :
    U7ObstructionEvolutionCalculus
      (TargetN rooted) (contributionMergeU7 rooted) where
  source := contributionMergeU7Source rooted
  compile := by
    intro indexedSupport indexedObstruction demand event
    rcases indexedSupport with ⟨oldSupport, mergePhase⟩
    rcases oldSupport with ⟨worldSupport, lossPhase⟩
    cases worldSupport with
    | inl oldSupport =>
        exact
          { disposition := .redirected ⟨(), rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred () rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | inr direction =>
        cases direction
        exact
          { disposition := .redirected
              ⟨GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget (),
                rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred
                (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
                rfl rfl (Nat.le_refl _), rfl⟩ }

def contributionMergeTheory
    (rooted : RootedFailure) : TheoryState (TargetN rooted) :=
  TheoryState.rootSemantic (TargetN rooted)

def contributionMergeInquiryAuditAt
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    SourceNativeInquiryFrontAuditAt
      (contributionMergeU7 rooted) (contributionMergeCalculus rooted)
      (contributionMergeTheory rooted)
      (contributionMergeSupportAt rooted current) :=
  .answered

/-- The contribution-action coordinate is distinct from obstruction inquiry.
Its front audit is answered because the exact compiler branch is an actual
action, not a U7/U8 search branch. -/
def contributionMergeActionAudit
    (rooted : RootedFailure) :
    SourceNativeInquiryFrontAuditAt
      (contributionMergeU7 rooted) (contributionMergeCalculus rooted)
      (contributionMergeTheory rooted)
      (contributionMergeTargetSupport rooted) :=
  .answered

/-! ## Five exact projection faces -/

/-- The root projection exposes the literal whole-ledger compiler image and
the lifecycle obligation of every row in that same occurrence.  The function
is only over the current complete ledger fibre; it is not a registry or a
future table. -/
def ContributionMergeRootPayloadAt
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt
        current) : Type :=
  SourceNativeLedgerEvolutionAt (contributionMergeSource rooted) occurrence ×
    ((entry : OpenResponsibilityAt (TargetN rooted)
      ((contributionMergeSource rooted).toRootSource.account.supportOf
        occurrence)) →
      AdmittedObligation (ContributionMergeLifecycleV rooted))

inductive ContributionMergeProjection
  | ledgerLifecycle
  | inquiry
  | answer
  | consumer
  | contributionAction

def contributionMergeProjectionLaw
    (rooted : RootedFailure) :
    SourceNativeProjectionLaw
      (contributionMergeRestructuringSource rooted).toLedgerSource where
  Projection := ContributionMergeProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .ledgerLifecycle => ContributionMergeRootPayloadAt rooted occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (contributionMergeInquiryEntryAt rooted current) ()
          (ULift.up.{1, 0} occurrence)
          (contributionMergeInquiryAuditAt rooted current) PUnit
    | .answer => PUnit
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence)
          (contributionMergeInquiryEntryAt rooted current) PUnit.unit
    | .contributionAction => match current with
      | 0 => PUnit
      | _ + 1 => SourceNativeInquiryCompilationTokenAt
          (mergedContributionEntry rooted) ()
          (ULift.up.{1, 0} occurrence)
          (contributionMergeActionAudit rooted) PUnit
  project := fun projection {current} occurrence _ => by
    cases projection with
    | ledgerLifecycle =>
        exact
          ⟨(contributionMergeLedgerCompiler rooted).compile occurrence,
            fun entry => contributionMergeObligationAt rooted
              occurrence.2.materialWitness entry⟩
    | inquiry => exact .canonical PUnit.unit
    | answer => exact PUnit.unit
    | consumer => exact .canonical
    | contributionAction =>
        cases current with
        | zero => exact PUnit.unit
        | succ current => exact .canonical PUnit.unit

/-! ## Complete authority and living root -/

def contributionMergeAuthoritySource
    (rooted : RootedFailure) :
    SourceNativeAuthoritySource (TargetN rooted) (TargetV rooted) where
  restructuringSource := contributionMergeRestructuringSource rooted
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (contributionMergeRestructuringSource rooted)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := TheoryState.rootSemantic (TargetN rooted)
  projectionLaw := contributionMergeProjectionLaw rooted

def contributionMergeAuthoritativeRoot
    (rooted : RootedFailure) :
    SourceNativeAuthoritativeRootClosure (TargetN rooted) (TargetV rooted) where
  source := contributionMergeAuthoritySource rooted
  emitted := contributionMergeEmitted rooted
  compiler_commutes := contributionMergeCompiler_commutes rooted

def contributionMergeLivingRoot
    (rooted : RootedFailure) :
    SourceNativeLivingRootClosure (TargetN rooted) (TargetV rooted) :=
  (contributionMergeAuthoritativeRoot rooted).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem contributionMergeRoot_lawSurface_exact
    (rooted : RootedFailure) :
    (contributionMergeLivingRoot rooted).source.base.lawSurface =
      TheoryState.rootSemantic (TargetN rooted) :=
  rfl

@[simp] theorem contributionMergeRoot_emitted_exact
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    (contributionMergeLivingRoot rooted).emitted current =
      contributionMergeEmitted rooted current :=
  rfl

/-! ## Root-native answer, consumer and compilation faces -/

abbrev ContributionMergeRootVisit
    (rooted : RootedFailure) :=
  SourceNativeTemporalVisitAt
    (contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot

def contributionMergeRootInquiryEventAt
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted) : Type 1 :=
  ULift.{1, 0}
    ((contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
      |>.source.source.toRootSource.actual.OccurrenceAt visit.current)

def contributionMergeRootInquiryEvent
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted) :
    contributionMergeRootInquiryEventAt rooted visit :=
  ULift.up.{1, 0} ((contributionMergeLivingRoot rooted).emitted visit.current)

def contributionMergeAnswerFaceAt
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted) :
    SourceNativeRootSemanticFaceAt
      (contributionMergeLivingRoot rooted) visit where
  projection := .answer
  active := PUnit.unit
  classifier_eq := rfl

def contributionMergeAnswerConsumerAt
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionMergeRootInquiryEvent rooted visit)
      (contributionMergeInquiryEntryAt rooted visit.current)
      (contributionMergeAnswerFaceAt rooted visit) where
  projection := .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionMergeAnsweredCompilationAt
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionMergeLivingRoot rooted) visit
      (contributionMergeInquiryEntryAt rooted visit.current)) :
    SourceNativeInquiryCompilationAt
      (contributionMergeLivingRoot rooted) visit
      (contributionMergeU7 rooted) (contributionMergeCalculus rooted)
      (contributionMergeTheory rooted) ()
      (contributionMergeRootInquiryEvent rooted visit)
      (contributionMergeInquiryEntryAt rooted visit.current) authority :=
  .answered (contributionMergeAnswerFaceAt rooted visit)
    (contributionMergeAnswerConsumerAt rooted visit)

/-- Installed inquiry face for an already generated causal-row authority.
It does not create a compilation program or state; the downstream runtime
must still obtain `authority` from the sequential action target. -/
def contributionMergeInquiryCompilationFaceAt
    (rooted : RootedFailure)
    (visit : ContributionMergeRootVisit rooted)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionMergeLivingRoot rooted) visit
      (contributionMergeInquiryEntryAt rooted visit.current)) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (contributionMergeLivingRoot rooted) visit ()
      (contributionMergeRootInquiryEvent rooted visit)
      (contributionMergeInquiryEntryAt rooted visit.current) authority
      (contributionMergeAnsweredCompilationAt rooted visit authority) where
  projection := .inquiry
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

/-! ## Initial conservative ledger and first actual write -/

abbrev contributionMergeRootInitialVisit
    (rooted : RootedFailure) :
    SourceNativeTemporalVisitAt
      (contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (contributionMergeLivingRoot rooted).toAuthoritativeRoot.toRoot.initialVisit

def contributionMergeRootInitialGenerated
    (rooted : RootedFailure) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
      (contributionMergeRootInitialVisit rooted) :=
  (contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit (contributionMergeRootInitialVisit rooted)

@[simp] theorem contributionMergeRoot_initialOccurrence_exact
    (rooted : RootedFailure) :
    (contributionMergeRootInitialGenerated rooted).occurrence =
      contributionMergeEmitted rooted 0 :=
  rfl

theorem contributionMergeRoot_initialLedger_exact
    (rooted : RootedFailure) :
    (⟨(contributionMergeLivingRoot rooted).toAuthoritativeRoot.toLedgerRoot
      |>.source.source.toRootSource.account.supportOf
        (contributionMergeRootInitialGenerated rooted).occurrence⟩ :
      CompleteLiveLedgerAt (TargetN rooted)) =
      contributionMergeInitialLedger rooted :=
  rfl

def contributionMergeRootInitialChildARow
    (rooted : RootedFailure) :
    (contributionMergeRootInitialGenerated rooted).GeneratedEntryRowAt
      (initialChildA rooted) :=
  ((contributionMergeRootInitialGenerated rooted).canonicalGeneratedEntryRow?
    (initialChildA rooted)).get (by rfl)

def contributionMergeRootInitialChildBRow
    (rooted : RootedFailure) :
    (contributionMergeRootInitialGenerated rooted).GeneratedEntryRowAt
      (initialChildB rooted) :=
  ((contributionMergeRootInitialGenerated rooted).canonicalGeneratedEntryRow?
    (initialChildB rooted)).get (by rfl)

def contributionMergeRootInitialObstructionRow
    (rooted : RootedFailure) :
    (contributionMergeRootInitialGenerated rooted).GeneratedEntryRowAt
      (initialObstruction rooted) :=
  ((contributionMergeRootInitialGenerated rooted).canonicalGeneratedEntryRow?
    (initialObstruction rooted)).get (by rfl)

/-- The root consumes the compiler's existing successor token; it does not
construct a second write or target. -/
def contributionMergeRootFirstSuccessor
    (rooted : RootedFailure) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionMergeRootInitialGenerated rooted).occurrence
      (contributionMergeRootInitialGenerated rooted).wholeLedgerWriteBack :=
  contributionMergeFirstSuccessor rooted

@[simp] theorem contributionMergeRoot_firstTargetCurrent_exact
    (rooted : RootedFailure) :
    (contributionMergeRootFirstSuccessor rooted).targetCurrent = 1 :=
  rfl

@[simp] theorem contributionMergeRoot_firstTargetOccurrence_exact
    (rooted : RootedFailure) :
    (contributionMergeRootFirstSuccessor rooted).targetOccurrence =
      contributionMergeEmitted rooted 1 :=
  rfl

theorem contributionMergeRoot_firstEvolution_exact
    (rooted : RootedFailure) :
    HEq (contributionMergeRootFirstSuccessor rooted).ledgerEvolution
      (contributionMergeFirstEvolution rooted
        (contributionMergeEmitted rooted 0)) :=
  HEq.rfl

theorem contributionMergeRoot_firstTargetLedger_exact
    (rooted : RootedFailure) :
    (⟨(contributionMergeRestructuringSource rooted).source.toRootSource
      |>.account.supportOf
        (contributionMergeRootFirstSuccessor rooted).targetOccurrence⟩ :
      CompleteLiveLedgerAt (TargetN rooted)) =
      contributionMergeTargetLedger rooted :=
  rfl

@[simp] theorem contributionMergeRoot_childA_destination_exact
    (rooted : RootedFailure) :
    ((contributionMergeRootFirstSuccessor rooted).ledgerEvolution.destination
      (initialChildA rooted)).1 = mergedContributionEntry rooted :=
  contributionMergeFirst_destination_childA rooted
    (contributionMergeEmitted rooted 0)

@[simp] theorem contributionMergeRoot_childB_destination_exact
    (rooted : RootedFailure) :
    ((contributionMergeRootFirstSuccessor rooted).ledgerEvolution.destination
      (initialChildB rooted)).1 = mergedContributionEntry rooted :=
  contributionMergeFirst_destination_childB rooted
    (contributionMergeEmitted rooted 0)

@[simp] theorem contributionMergeRoot_obstruction_destination_exact
    (rooted : RootedFailure) :
    ((contributionMergeRootFirstSuccessor rooted).ledgerEvolution.destination
      (initialObstruction rooted)).1 = mergedObstructionEntry rooted :=
  contributionMergeFirst_destination_obstruction rooted
    (contributionMergeEmitted rooted 0)

/-! ## Projection readouts -/

def contributionMergeRootInitialProjectionPayload
    (rooted : RootedFailure) :
    ContributionMergeRootPayloadAt rooted
      (contributionMergeEmitted rooted 0) :=
  (contributionMergeAuthoritySource rooted).projectionLaw.project
    .ledgerLifecycle (contributionMergeEmitted rooted 0) PUnit.unit

@[simp] theorem contributionMergeRoot_projectionLedger_exact
    (rooted : RootedFailure) :
    (contributionMergeRootInitialProjectionPayload rooted).1 =
      (contributionMergeLedgerCompiler rooted).compile
        (contributionMergeEmitted rooted 0) :=
  rfl

@[simp] theorem contributionMergeRoot_projectionChildAObligation_exact
    (rooted : RootedFailure) :
    (contributionMergeRootInitialProjectionPayload rooted).2
        (initialChildA rooted) =
      contributionMergeObligationAt rooted
        exactSourceGeneratedLossAllocationMaterialWitness
        (initialChildA rooted) :=
  rfl

@[simp] theorem contributionMergeRoot_projectionChildBObligation_exact
    (rooted : RootedFailure) :
    (contributionMergeRootInitialProjectionPayload rooted).2
        (initialChildB rooted) =
      contributionMergeObligationAt rooted
        exactSourceGeneratedLossAllocationMaterialWitness
        (initialChildB rooted) :=
  rfl

def contributionMergeRootInquiryProjectionPayload
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    SourceNativeInquiryCompilationTokenAt
      (contributionMergeInquiryEntryAt rooted current) ()
      (ULift.up.{1, 0} (contributionMergeEmitted rooted current))
      (contributionMergeInquiryAuditAt rooted current) PUnit :=
  (contributionMergeAuthoritySource rooted).projectionLaw.project
    .inquiry (contributionMergeEmitted rooted current) PUnit.unit

@[simp] theorem contributionMergeRoot_inquiryProjection_exact
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    contributionMergeRootInquiryProjectionPayload rooted current =
      SourceNativeInquiryCompilationTokenAt.canonical PUnit.unit :=
  rfl

def contributionMergeRootAnswerProjectionPayload
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) : PUnit :=
  (contributionMergeAuthoritySource rooted).projectionLaw.project
    .answer (contributionMergeEmitted rooted current) PUnit.unit

@[simp] theorem contributionMergeRoot_answerProjection_exact
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    contributionMergeRootAnswerProjectionPayload rooted current = PUnit.unit :=
  rfl

def contributionMergeRootConsumerProjectionPayload
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    SourceNativeInquiryAnswerConsumerTokenAt
      () (ULift.up.{1, 0} (contributionMergeEmitted rooted current))
      (contributionMergeInquiryEntryAt rooted current) PUnit.unit :=
  (contributionMergeAuthoritySource rooted).projectionLaw.project
    .consumer (contributionMergeEmitted rooted current) PUnit.unit

@[simp] theorem contributionMergeRoot_consumerProjection_exact
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    contributionMergeRootConsumerProjectionPayload rooted current =
      SourceNativeInquiryAnswerConsumerTokenAt.canonical :=
  rfl

end
end M14SourceGeneratedContributionMergeRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeInquiryCompilationFaceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeRoot_inquiryProjection_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeRootInitialChildARow
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeRootFirstSuccessor
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRoot.contributionMergeRoot_firstEvolution_exact
