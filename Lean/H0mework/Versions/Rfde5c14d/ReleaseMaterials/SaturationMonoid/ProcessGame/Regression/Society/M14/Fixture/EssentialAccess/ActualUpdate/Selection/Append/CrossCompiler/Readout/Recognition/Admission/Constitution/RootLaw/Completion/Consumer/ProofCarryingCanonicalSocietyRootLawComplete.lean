import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Constitution.RootLaw.Completion.Bridge.Consumer.ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Proposal.Recourse.Constitution.Consumer.ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourseConstitution

/-!
# Canonical Society root-law completion

The final M14 mouth separates runtime openness from theorem completion.  Every
raw submission has one unified four-class final outcome: presentation, typed
rejection with visible bearer, installed rooted action with whole-ledger next,
or exact external failure/U8.  The local action class is constructively empty
at this root; every complete installed execution, whenever present, also
retains the generic four-class theorem and exact conditional U8.

The certificate is not vacuous: the same cofinal point retains the last
first-refusal recourse debt, a premise-free rooted/external whole-ledger/U8
leaf, an actual canonical enactment, an ordinary repair next, the existing
self-U8 tick and the no-unrevisable-law control.  No application catalogue or
completed future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyRootLawComplete

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion
open M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourseConstitution

universe uVisible uOutput uEffect

/-- Actual M14 anchor for the final universal mouth.  Runtime openness remains
in `selfU8Tick`; theorem completion is the exhaustion/no-fifth law exported
below, not an enumeration of later applications. -/
structure CanonicalSocietyRootLawCompletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  private mk ::
  priorPoint : CanonicalCofinalFirstRefusalSourceOwnedRecourseAt point
  canonicalActualRootedExternal :
    Nonempty
      (RawRootedExternalWholeLedgerU8At
        (universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
          (cycleLifecycleIndex initial m) .actual).generate)
  actualRefusalRecourse :
    type_of%
      (priorPoint.sourceOwnedRecourse.everyFuelHasActualRefusalRecourse 0)
  actualCanonicalEnactment :
    type_of% actualRefusalRecourse.canonicalLegislationStillGeneratesNext
  actualOrdinaryWholeLedgerWrite :
    type_of% actualRefusalRecourse.ordinaryWholeLedgerWriteBack
  actualOrdinaryGeneratedNext :
    type_of% actualRefusalRecourse.ordinaryActualRepairNext
  actualU8Tick : ExactCanonicalSelfU8TickAt initial m
  noUnrevisableRuntime : type_of% point.runtimeFinalityReportEmpty

theorem canonicalSocietyRootLawCompletion_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalSocietyRootLawCompletionAt point := by
  let prior :=
    canonicalCofinalFirstRefusalSourceOwnedRecourse_directConsumer point
  let actual := prior.sourceOwnedRecourse.everyFuelHasActualRefusalRecourse 0
  exact
    { priorPoint := prior
      canonicalActualRootedExternal :=
        canonicalActualRootedExternal_nonempty oldVisit sourceIndex
          (cycleLifecycleIndex initial m)
      actualRefusalRecourse := actual
      actualCanonicalEnactment :=
        actual.canonicalLegislationStillGeneratesNext
      actualOrdinaryWholeLedgerWrite := actual.ordinaryWholeLedgerWriteBack
      actualOrdinaryGeneratedNext := actual.ordinaryActualRepairNext
      actualU8Tick := point.selfU8Tick
      noUnrevisableRuntime := point.runtimeFinalityReportEmpty }

/-- M∞-specialized spelling of per-program root-law completion. -/
abbrev CanonicalSocietyRootLawCompleteAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    (program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram) : Prop :=
  SourceNativeRootLawCompleteAt program.generate

/-- M∞-specialized spelling of permanent conditional U8 availability. -/
abbrev CanonicalSocietyU8AvailableAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    (program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram) : Prop :=
  SourceNativeU8AvailableAt program.generate

/-- M∞ root-law completion does not require a caller to exhibit a local
legislation program.  It stores the nonempty rooted/external leaf, classifies
every raw generated submission, and universally consumes every complete
installed program if one exists at any legal visit. -/
structure CanonicalSocietyMInfinityRootLawCompleteAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point) : Prop where
  private mk ::
  canonicalRootedExternal :
    type_of% completion.canonicalActualRootedExternal
  everyRawSubmission :
    ∀ (index : Nat)
      (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
        ).law.vocabulary.Scenario)
      {Visible : Type uVisible} {Output : Type uOutput}
      {ClaimedEffect : Type uEffect}
      {attempt : SourceNativeObserverConsumerAttemptAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) scenario
        Visible Output ClaimedEffect}
      {submissionProgram :
        SourceNativeObserverConsumerSubmissionProgramAt attempt}
      {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
      (generated : SourceGeneratedObserverConsumerSubmissionAt
        submissionProgram material),
      CanonicalSocietyRawAttemptRootLawCompleteAt generated
  everyInstalledProgram :
    ∀ (index : Nat)
      (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
        ).law.vocabulary.Scenario)
      {Visible : Type uVisible} {Output : Type uOutput}
      {ClaimedEffect : Type uEffect}
      {attempt : SourceNativeObserverConsumerAttemptAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) scenario
        Visible Output ClaimedEffect}
      {submissionProgram :
        SourceNativeObserverConsumerSubmissionProgramAt attempt}
      (program : SourceNativeObserverConsumerLegislationProgramAt
        submissionProgram),
      CanonicalSocietyRootLawCompleteAt program

/-- Permanent U8 availability has the same two layers: rooted raw attempts
enter the exact external self-U8 bridge, while any installed complete program
retains the compiler-selected same-occurrence conditional U8 theorem. -/
structure CanonicalSocietyMInfinityU8AvailableAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point) : Prop where
  private mk ::
  everyRawSubmission :
    ∀ (index : Nat)
      (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
        ).law.vocabulary.Scenario)
      {Visible : Type uVisible} {Output : Type uOutput}
      {ClaimedEffect : Type uEffect}
      {attempt : SourceNativeObserverConsumerAttemptAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) scenario
        Visible Output ClaimedEffect}
      {submissionProgram :
        SourceNativeObserverConsumerSubmissionProgramAt attempt}
      {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
      (generated : SourceGeneratedObserverConsumerSubmissionAt
        submissionProgram material),
      CanonicalSocietyRawAttemptU8AvailableAt generated
  everyInstalledProgram :
    ∀ (index : Nat)
      (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
        ).law.vocabulary.Scenario)
      {Visible : Type uVisible} {Output : Type uOutput}
      {ClaimedEffect : Type uEffect}
      {attempt : SourceNativeObserverConsumerAttemptAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) scenario
        Visible Output ClaimedEffect}
      {submissionProgram :
        SourceNativeObserverConsumerSubmissionProgramAt attempt}
      (program : SourceNativeObserverConsumerLegislationProgramAt
        submissionProgram),
      CanonicalSocietyU8AvailableAt program

namespace CanonicalSocietyRootLawCompletionAt

/-- Raw bodies never become a fifth authority class.  Presentation and
rejection retain the empty local fibre; rooted authority already carries the
source-owned external whole-ledger/U8 bridge. -/
theorem everyRawSubmission_exhaustive
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    Nonempty (RawLawfulPresentationNoWriteAt generated) ∨
      Nonempty (RawTypedRejectionVisibleResidualAt generated) ∨
        Nonempty (RawRootedInstalledActionWholeLedgerNextAt generated) ∨
          Nonempty (RawRootedExternalWholeLedgerU8At generated) := by
  cases completion
  exact rawAttempt_richExhaustive generated

/-- Complete installed programs retain the independent four-class theorem.
This is a conditional consumer, not the non-vacuity witness for M∞. -/
theorem everyInstalledProgram_rootLawComplete_and_u8Available
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    (program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram) :
    CanonicalSocietyRootLawCompleteAt program ∧
      CanonicalSocietyU8AvailableAt program := by
  cases completion
  exact ⟨sourceNativeRootLawComplete program.generate,
    sourceNativeU8Available program.generate⟩

/-- Final non-vacuous universal mouth.  It quantifies an arbitrary raw
submission, returns exact completion plus conditional U8 availability, and
retains one premise-free inhabited rooted/external leaf at the same M∞ point. -/
theorem everyRawSubmission_rootLawComplete_and_u8Available
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt
      submissionProgram material) :
    CanonicalSocietyRawAttemptRootLawCompleteAt generated ∧
      CanonicalSocietyRawAttemptU8AvailableAt generated ∧
        Nonempty
          (RawRootedExternalWholeLedgerU8At
            (universalSocietyCertifiedRootAuthorityProgramAt oldVisit
              sourceIndex (cycleLifecycleIndex initial m) .actual).generate) := by
  let raw := rawAttempt_rootLawComplete_and_u8Available generated
  exact ⟨raw.1, raw.2, completion.canonicalActualRootedExternal⟩

/-- The final universal mouth.  No raw body, local program or future
application is supplied to inhabit it.  The two fields are theorem schemas
over all later legal attempts, while the root-law half retains the concrete
rooted/external inhabitant at this cofinal point. -/
theorem rootLawComplete_and_u8Available
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point) :
    CanonicalSocietyMInfinityRootLawCompleteAt completion ∧
      CanonicalSocietyMInfinityU8AvailableAt completion := by
  constructor
  · refine
      { canonicalRootedExternal := completion.canonicalActualRootedExternal
        everyRawSubmission := ?_
        everyInstalledProgram := ?_ }
    · intro index scenario _ _ _ _ _ _ generated
      exact
        (completion.everyRawSubmission_rootLawComplete_and_u8Available
          index scenario generated).1
    · intro index scenario _ _ _ _ _ program
      exact
        (completion.everyInstalledProgram_rootLawComplete_and_u8Available
          index scenario program).1
  · refine
      { everyRawSubmission := ?_
        everyInstalledProgram := ?_ }
    · intro index scenario _ _ _ _ _ _ generated
      exact
        (completion.everyRawSubmission_rootLawComplete_and_u8Available
          index scenario generated).2.1
    · intro index scenario _ _ _ _ _ program
      exact
        (completion.everyInstalledProgram_rootLawComplete_and_u8Available
          index scenario program).2

/-- No-fifth direct consumer at the final raw mouth. -/
theorem noFifthOffLedgerAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt
      submissionProgram material) :
    CanonicalSocietyRawAttemptRootLawCompleteAt generated :=
  (completion.everyRawSubmission_rootLawComplete_and_u8Available index
    scenario generated).1

/-- No-fifth theorem for any already source-installed complete program. -/
theorem installedProgram_hasNoFifthClass
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    (program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram) :
    type_of%
      (compiledObserverConsumerLegislation_hasNoFifthClass program.generate) :=
  (completion.everyInstalledProgram_rootLawComplete_and_u8Available index
    scenario program).1
    |>.noFifthClass

/-- Exact negative controls: neither presentation nor rejection can write,
and the two writing leaves cannot occur together. -/
theorem installedProgram_nonWritingAndWritingDisjointControls
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    {point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse}
    (completion : CanonicalSocietyRootLawCompletionAt point)
    (index : Nat)
    (scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario)
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    (program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram) :
    let complete :=
      (completion.everyInstalledProgram_rootLawComplete_and_u8Available index
        scenario program).1
    type_of% complete.presentationCannotWrite ∧
      type_of% complete.rejectionCannotWrite ∧
      type_of% complete.actionAndU8Disjoint := by
  dsimp only
  let complete :=
    (completion.everyInstalledProgram_rootLawComplete_and_u8Available index
      scenario program).1
  exact ⟨complete.presentationCannotWrite, complete.rejectionCannotWrite,
    complete.actionAndU8Disjoint⟩

end CanonicalSocietyRootLawCompletionAt

end
end M14ProofCarryingCanonicalSocietyRootLawComplete
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.canonicalSocietyRootLawCompletion_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.everyRawSubmission_exhaustive
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.rootLawComplete_and_u8Available
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.noFifthOffLedgerAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.everyInstalledProgram_rootLawComplete_and_u8Available
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.installedProgram_hasNoFifthClass
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRootLawComplete.CanonicalSocietyRootLawCompletionAt.installedProgram_nonWritingAndWritingDisjointControls
