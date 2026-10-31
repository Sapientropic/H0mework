import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendStage
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedSequentialCriticalActionAppendTarget

/-!
# Source-generated sequential cross-compiler relation append

Every heterogeneous stage compiles one exact actual action whose target
vocabulary has the next coproduct atom type.  The target initial contains only
the complete left-embedded prior; its first whole-ledger write generates the
right root.  The public mouth accepts depth only and every target, action,
receipt and next is a dependent readout of the exact source occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialCrossCompilerRelationAppend

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedSequentialCriticalActionAppendTarget
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt

abbrev appendStageAt (depth : Nat) :=
  crossCompilerRelationAppendStageAt depth

def crossCompilerSelectedEventAt (depth : Nat) : EssentialAccessEvent :=
  (crossCompilerCurrentStageAt depth).targetSeed.1

def crossCompilerSelectedActionAt (depth : Nat) :
    SourceGeneratedEssentialAccessCriticalActionAt
      (crossCompilerSelectedEventAt depth) :=
  sourceGeneratedEssentialAccessCriticalActionAt
    (crossCompilerSelectedEventAt depth)

def crossCompilerSelectedUpdateAt (depth : Nat) :
    EssentialAccessCriticalActualUpdateAt
      (crossCompilerSelectedEventAt depth) :=
  sourceGeneratedEssentialAccessCriticalActualUpdateAt
    (crossCompilerSelectedEventAt depth)

theorem crossCompilerSelectedAction_seed_exact (depth : Nat) :
    (crossCompilerSelectedActionAt depth
      ).criticalBearer.bearerLineage.seed =
      (crossCompilerCurrentStageAt depth).targetSeed := by
  change exactEssentialAccessSeed
    (crossCompilerCurrentStageAt depth).targetSeed.1 =
      (crossCompilerCurrentStageAt depth).targetSeed
  exact exactEssentialAccessSeed_of_exact
    (crossCompilerCurrentStageAt depth).targetSeed

theorem crossCompilerSelectedAction_directConsumer (depth : Nat) :
    (crossCompilerSelectedActionAt depth
      ).criticalBearer.bearerLineage.seed =
        (crossCompilerCurrentStageAt depth).targetSeed ∧
      (crossCompilerSelectedActionAt depth).criticalBearer.commonBearer =
        (criticalRelationObligation essentialAccessCriticalBearerOf
          (crossCompilerSelectedEventAt depth)).bearer ∧
      essentialAccessRelationCompiler.phaseStep
          (essentialAccessCriticalRelation
            (crossCompilerSelectedEventAt depth)) ≠ 0 ∧
      essentialAccessRelationCompiler.roleAt
          (essentialAccessCriticalRelation
            (crossCompilerSelectedEventAt depth)) .target =
        essentialAccessRelationCompiler.advanceRole
          Lifecycle.actualEventGame.source
          (essentialAccessRelationCompiler.phaseStep
            (essentialAccessCriticalRelation
              (crossCompilerSelectedEventAt depth)))
          (essentialAccessRelationCompiler.roleAt
            (essentialAccessCriticalRelation
              (crossCompilerSelectedEventAt depth)) .source) :=
  ⟨crossCompilerSelectedAction_seed_exact depth,
    (sourceGeneratedEssentialAccessCriticalActualUpdateAt
      (crossCompilerSelectedEventAt depth)).bearerCommutes,
    essentialAccessCriticalPhase_nonzero _, rfl⟩

def crossCompilerRelationAppendTargetRootAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :=
  rootedAppendLivingRoot (appendStageAt depth).sourceRoot
    exactSource.occurrence (appendStageAt depth).targetPrior
      (appendStageAt depth).targetAtom

def crossCompilerRelationAppendOccurrencePresentationAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    ConstructivePresentation
      ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (appendStageAt depth).sourceVisit.current)
      ((crossCompilerRelationAppendTargetRootAt depth exactSource
        ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (appendStageAt depth).targetPrior) :=
  { forward := fun _ =>
      (crossCompilerRelationAppendTargetRootAt depth exactSource).emitted
        (appendStageAt depth).targetPrior
    backward := fun _ =>
      (appendStageAt depth).sourceRoot.emitted
        (appendStageAt depth).sourceVisit.current
    backward_forward := fun occurrence =>
      ((appendStageAt depth).sourceOccurrenceUnique occurrence).symm
    forward_backward := by
      intro occurrence
      rcases occurrence with ⟨support, event⟩
      cases support with
      | inl old => exact nomatch event
      | inr direction => cases direction; cases event; rfl }

def crossCompilerRelationAppendTargetInitialVisitAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    SourceNativeTemporalVisitAt
      (crossCompilerRelationAppendTargetRootAt depth exactSource
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (crossCompilerRelationAppendTargetRootAt depth exactSource
    ).toAuthoritativeRoot.toRoot.initialVisit

def crossCompilerRelationAppendTargetInitialGeneratedAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :=
  (crossCompilerRelationAppendTargetRootAt depth exactSource
    ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (crossCompilerRelationAppendTargetInitialVisitAt depth exactSource)

def crossCompilerRelationAppendTargetEntryRowAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
      ).GeneratedEntryRowAt newRevisedEntry :=
  ((crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
    ).canonicalGeneratedEntryRow? newRevisedEntry).get (by rfl)

def crossCompilerRelationAppendTargetFirstSuccessorAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    SourceNativeLedgerGeneratedSuccessorAt
      (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
        ).occurrence
      (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
        ).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
      ).wholeLedgerWriteBack).get (by rfl)

structure CrossCompilerRelationAppendReceiptCoreAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) : Prop where
  sourceCanonical : exactSource = (appendStageAt depth).exactSource
  sourceCurrentExact : HEq (appendStageAt depth).sourceVisit.current
    (crossCompilerCurrentStageAt depth).actionCurrent
  sourceEntryExact : HEq (appendStageAt depth).sourceEntry newRevisedEntry
  targetInitialLeft :
    (crossCompilerRelationAppendTargetRootAt depth exactSource
      ).toAuthoritativeRoot.toRoot.source.initial =
      (crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl
  targetFirstWrite :
    (crossCompilerRelationAppendTargetFirstSuccessorAt depth exactSource
      ).targetCurrent =
      (crossCompilerCurrentStageAt depth).targetCurrent
  targetRootRight :
    (crossCompilerCurrentStageAt depth).targetCurrent.root =
      .inr (crossCompilerCurrentStageAt depth).targetSeed
  targetBranchLeft :
    (crossCompilerCurrentStageAt depth).targetCurrent.branches =
      AccountedBranches.singleton
        ((crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl)
  targetSeedFromFold :
    (crossCompilerCurrentStageAt depth).targetSeed =
      crossCompilerCurrentSeedAt depth
        (crossCompilerCurrentStageAt depth).actionCurrent
  actionSeedExact :
    (crossCompilerSelectedActionAt depth
      ).criticalBearer.bearerLineage.seed =
      (crossCompilerCurrentStageAt depth).targetSeed
  phaseNonzero : essentialAccessRelationCompiler.phaseStep
    (essentialAccessCriticalRelation
      (crossCompilerSelectedEventAt depth)) ≠ 0
  targetRoleGenerated : essentialAccessRelationCompiler.roleAt
      (essentialAccessCriticalRelation
        (crossCompilerSelectedEventAt depth)) .target =
    essentialAccessRelationCompiler.advanceRole
      Lifecycle.actualEventGame.source
      (essentialAccessRelationCompiler.phaseStep
        (essentialAccessCriticalRelation
          (crossCompilerSelectedEventAt depth)))
      (essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation
          (crossCompilerSelectedEventAt depth)) .source)
  inheritedOutcomes : ∀ projection :
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection,
    HEq ((rootedAppendProjectionLaw (appendStageAt depth).sourceRoot
      exactSource.occurrence (appendStageAt depth).targetPrior
        (appendStageAt depth).targetAtom).outcomeAt
          (RootedAppendProjection.inherited projection)
          (rootedAppendEmitted (appendStageAt depth).targetPrior
            (appendStageAt depth).targetAtom
              (appendStageAt depth).targetPrior))
      ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection exactSource.occurrence)
  installedConsumer :
    installedRootedAppendConsumer (appendStageAt depth).sourceRoot
      exactSource.occurrence (appendStageAt depth).targetPrior
        (appendStageAt depth).targetAtom =
      SourceNativeInquiryAnswerConsumerTokenAt.canonical
  firstWholeSuccessor : Nonempty (SourceNativeLedgerGeneratedSuccessorAt
    (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
      ).occurrence
    (crossCompilerRelationAppendTargetInitialGeneratedAt depth exactSource
      ).wholeLedgerWriteBack)

theorem crossCompilerRelationAppendReceiptCoreAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    CrossCompilerRelationAppendReceiptCoreAt depth exactSource := by
  rw [exactSource.eq_generated]
  exact
    { sourceCanonical := rfl
      sourceCurrentExact := (appendStageAt depth).sourceCurrentExact
      sourceEntryExact := (appendStageAt depth).sourceEntryExact
      targetInitialLeft := rfl
      targetFirstWrite := by
        change rootedAppendNativeTarget
          (appendStageAt depth).targetPrior
          (appendStageAt depth).targetAtom
          (appendStageAt depth).targetPrior = _
        exact (rootedAppendNativeTarget_initial
          (appendStageAt depth).targetPrior
          (appendStageAt depth).targetAtom).trans
            (appendStageAt depth).targetCurrent_exact.symm
      targetRootRight :=
        crossCompilerCurrentStageAt_targetRoot_exact depth
      targetBranchLeft :=
        crossCompilerCurrentStageAt_targetBranches_exact depth
      targetSeedFromFold :=
        (crossCompilerCurrentStageAt depth).targetSeedExact
      actionSeedExact := crossCompilerSelectedAction_seed_exact depth
      phaseNonzero := essentialAccessCriticalPhase_nonzero _
      targetRoleGenerated := rfl
      inheritedOutcomes := fun projection =>
        rootedAppendInheritedProjection_outcome_exact
          (appendStageAt depth).sourceRoot
          (appendStageAt depth).exactSource.occurrence
          (appendStageAt depth).targetPrior
          (appendStageAt depth).targetAtom projection
          (rootedAppendEmitted (appendStageAt depth).targetPrior
            (appendStageAt depth).targetAtom
              (appendStageAt depth).targetPrior)
      installedConsumer := rfl
      firstWholeSuccessor :=
        ⟨crossCompilerRelationAppendTargetFirstSuccessorAt depth
          (appendStageAt depth).exactSource⟩ }

def ExactCrossCompilerRelationAppendReceiptAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit)
    (_answer : PUnit) : Type 3 :=
  ULift.{3, 0} (PLift (CrossCompilerRelationAppendReceiptCoreAt depth
    exactSource))

def crossCompilerRelationAppendTargetAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    SourceNativeSequentialActualActionTargetAt
      (appendStageAt depth).sourceRoot (appendStageAt depth).sourceVisit
      exactSource (appendStageAt depth).sourceEntry
        (appendStageAt depth).sourceAuthority :=
  { TargetN := NewN
    translation := sequentialCriticalActionAppendIdentityTranslation
    TargetV := RootedAppendVAt (appendStageAt depth).targetPrior
      (appendStageAt depth).targetAtom
    targetRoot := crossCompilerRelationAppendTargetRootAt depth exactSource
    targetTheory := revisedInquiryTheory
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic :=
      { compile := id
        commuting := fun _ => rfl }
    occurrencePresentation :=
      crossCompilerRelationAppendOccurrencePresentationAt depth exactSource
    occurrence_commutes := rfl
    initialSupport_heq := (appendStageAt depth).sourceInitialSupportHEq
    initialOpenLedger := (appendStageAt depth).sourceInitialOpenLedger
    initialOpenLedger_heq :=
      (appendStageAt depth).sourceInitialOpenLedgerHEq
    initialLedger_responsibility_commutes :=
      (appendStageAt depth).sourceInitialLedgerResponsibilityCommutes
    initialLedger_claim_commutes :=
      (appendStageAt depth).sourceInitialLedgerClaimCommutes
    initialLedger_budget_conservative :=
      (appendStageAt depth).sourceInitialLedgerBudgetConservative
    initialLedgerNoFresh :=
      (appendStageAt depth).sourceInitialLedgerNoFresh
    translatedSourceEntryRow := by
      rw [(appendStageAt depth).sourceEntryTargetExact]
      exact crossCompilerRelationAppendTargetEntryRowAt depth exactSource
    firstSuccessor :=
      crossCompilerRelationAppendTargetFirstSuccessorAt depth exactSource
    canonical_targetNextVisit_eq := rfl
    Answer := PUnit
    answer := PUnit.unit
    Receipt := ExactCrossCompilerRelationAppendReceiptAt depth exactSource
    receipt := ULift.up (PLift.up
      (crossCompilerRelationAppendReceiptCoreAt depth exactSource)) }

def crossCompilerRelationAppendProgramAt (depth : Nat) :
    SourceNativeSequentialActualActionProgramAt
      (appendStageAt depth).sourceRoot (appendStageAt depth).sourceVisit
      (appendStageAt depth).sourceEntry
        (appendStageAt depth).sourceAuthority where
  targetAt := crossCompilerRelationAppendTargetAt depth

/-- Zero-choice public action producer. -/
def generatedCrossCompilerRelationAppendActionAt (depth : Nat) :
    SourceGeneratedSequentialActualActionAt
      (crossCompilerRelationAppendProgramAt depth)
      (appendStageAt depth).exactSource :=
  (crossCompilerRelationAppendProgramAt depth).generate
    (appendStageAt depth).exactSource

def crossCompilerRelationAppendActualActionCompilationAt
    (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.toLedgerRoot
        (appendStageAt depth).sourceVisit) :
    SourceNativeInquiryCompilationAt
      (appendStageAt depth).sourceRoot (appendStageAt depth).sourceVisit
      revisedInquiryU7 revisedInquiryCalculus
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.lawSurface ()
      (ULift.up.{1, 0}
        ((appendStageAt depth).sourceRoot.emitted
          (appendStageAt depth).sourceVisit.current))
      (appendStageAt depth).sourceEntry
      (appendStageAt depth).sourceAuthority :=
  .actualAction ((crossCompilerRelationAppendProgramAt depth).generate
    exactSource)

def crossCompilerRelationAppendCompilationProgramAt (depth : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (appendStageAt depth).sourceRoot (appendStageAt depth).sourceVisit
      revisedInquiryU7 revisedInquiryCalculus
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.lawSurface ()
      (ULift.up.{1, 0}
        ((appendStageAt depth).sourceRoot.emitted
          (appendStageAt depth).sourceVisit.current))
      (appendStageAt depth).sourceEntry
      (appendStageAt depth).sourceAuthority where
  compile := crossCompilerRelationAppendActualActionCompilationAt depth

@[simp] theorem generatedCrossCompilerRelationAppendAction_targetRoot_exact
    (depth : Nat) :
    (generatedCrossCompilerRelationAppendActionAt depth).target.targetRoot =
      (appendStageAt depth).targetRoot :=
  rfl

theorem generatedCrossCompilerRelationAppendAction_macroNext_exact
    (depth : Nat) :
    (generatedCrossCompilerRelationAppendActionAt depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedCrossCompilerRelationAppendActionAt depth).target.TargetV,
        (generatedCrossCompilerRelationAppendActionAt depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedCrossCompilerRelationAppendActionAt depth
          ).target.targetVisit⟩ :=
  (generatedCrossCompilerRelationAppendActionAt depth).target
    |>.targetAnswerAndNext_next_eq

theorem generatedCrossCompilerRelationAppendAction_directConsumer
    (depth : Nat) :
    (generatedCrossCompilerRelationAppendActionAt depth
      ).target.targetRoot = (appendStageAt depth).targetRoot ∧
    (generatedCrossCompilerRelationAppendActionAt depth
      ).target.firstSuccessor.targetCurrent =
        (crossCompilerCurrentStageAt depth).targetCurrent ∧
    (crossCompilerCurrentStageAt depth).targetSeed =
      crossCompilerCurrentSeedAt depth
        (crossCompilerCurrentStageAt depth).actionCurrent ∧
    (crossCompilerSelectedActionAt depth
      ).criticalBearer.bearerLineage.seed =
        (crossCompilerCurrentStageAt depth).targetSeed ∧
    essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation
          (crossCompilerSelectedEventAt depth)) .target =
      essentialAccessRelationCompiler.advanceRole
        Lifecycle.actualEventGame.source
        (essentialAccessRelationCompiler.phaseStep
          (essentialAccessCriticalRelation
            (crossCompilerSelectedEventAt depth)))
        (essentialAccessRelationCompiler.roleAt
          (essentialAccessCriticalRelation
            (crossCompilerSelectedEventAt depth)) .source) ∧
    Nonempty ((generatedCrossCompilerRelationAppendActionAt depth
      ).target.Receipt
        (generatedCrossCompilerRelationAppendActionAt depth).answer) :=
  ⟨rfl,
    (generatedCrossCompilerRelationAppendActionAt depth
      ).receipt.down.down.targetFirstWrite,
    (generatedCrossCompilerRelationAppendActionAt depth
      ).receipt.down.down.targetSeedFromFold,
    (generatedCrossCompilerRelationAppendActionAt depth
      ).receipt.down.down.actionSeedExact,
    (generatedCrossCompilerRelationAppendActionAt depth
      ).receipt.down.down.targetRoleGenerated,
    ⟨(generatedCrossCompilerRelationAppendActionAt depth).receipt⟩⟩

end
end M14SourceGeneratedSequentialCrossCompilerRelationAppend
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.generatedCrossCompilerRelationAppendActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.generatedCrossCompilerRelationAppendAction_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend.generatedCrossCompilerRelationAppendAction_macroNext_exact
