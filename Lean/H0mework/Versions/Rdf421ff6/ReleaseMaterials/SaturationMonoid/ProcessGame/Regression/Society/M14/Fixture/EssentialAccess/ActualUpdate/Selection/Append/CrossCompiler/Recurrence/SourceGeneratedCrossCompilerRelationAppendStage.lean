import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationCurrentRecurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.Generic.SourceGeneratedRootedAccountedUnfoldingAppendContinuation

/-!
# Source-generated heterogeneous relation append stage

This stage ties the growing coproduct current to one actual living root.  Its
target root is generated from the exact source occurrence by the unique
polymorphic append ledger.  The next stage reuses that target root and its
retained visit; it stores no caller current, target shell, event table or
completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerRelationAppendStage

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedSequentialCriticalActionAppendTarget
open M14SourceGeneratedCriticalActionAppendContinuation
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrenceStage.RelationLineageRecurrenceStage
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
open M14SourceGeneratedRootedAccountedUnfoldingAppendContinuation

/-- The structure stores only the exact source-side decomposition.  Target
vocabulary, root and visits are generated functions of these fields and the
global current recurrence at the same depth. -/
structure CrossCompilerRelationAppendStageAt (depth : Nat) : Type 15 where
  private mk ::
  SourceV : ConstructiveRoot.Vocabulary
  sourceRoot : SourceNativeLivingRootClosure NewN SourceV
  sourceVisit : SourceNativeTemporalVisitAt
    sourceRoot.toAuthoritativeRoot.toLedgerRoot
  sourceEntry : OpenResponsibilityAt NewN
    (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (sourceRoot.emitted sourceVisit.current))
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    sourceRoot sourceVisit sourceEntry
  sourceLawSurfaceEq :
    sourceRoot.toAuthoritativeRoot.source.lawSurface = revisedInquiryTheory
  sourceOccurrenceUnique :
    (occurrence :
      sourceRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        sourceVisit.current) →
      occurrence = sourceRoot.emitted sourceVisit.current
  sourceSupportExact :
    sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (sourceRoot.emitted sourceVisit.current) =
        minimalCoface.cofaceSupport
  sourceInitialSupportHEq : HEq minimalCoface.cofaceSupport
    (sequentialCriticalActionAppendIdentityTranslation.support.forward
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current)))
  sourceInitialOpenLedger : ConstructiveRetract
    (OpenResponsibilityAt NewN
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current)))
    (OpenResponsibilityAt NewN minimalCoface.cofaceSupport)
  sourceInitialOpenLedgerHEq : HEq sourceInitialOpenLedger
    (sequentialCriticalActionAppendIdentityTranslation.oldOpenLedger
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current)))
  sourceInitialLedgerResponsibilityCommutes :
    (entry : OpenResponsibilityAt NewN
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))) →
      sequentialCriticalActionAppendIdentityTranslation.responsibility.forward
          entry.1 =
        (sourceInitialOpenLedger.forward entry).1
  sourceInitialLedgerClaimCommutes :
    (entry : OpenResponsibilityAt NewN
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))) →
      sequentialCriticalActionAppendIdentityTranslation.claim.forward
          entry.claim =
        (sourceInitialOpenLedger.forward entry).claim
  sourceInitialLedgerBudgetConservative :
    (entry : OpenResponsibilityAt NewN
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))) →
      (sourceInitialOpenLedger.forward entry).progressBudget ≤
        entry.progressBudget
  sourceInitialLedgerNoFresh :
    (targetEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt NewN
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (sourceRoot.emitted sourceVisit.current)) =>
        PLift (sourceInitialOpenLedger.forward oldEntry = targetEntry))
  sourceEntryTargetExact :
    sourceInitialOpenLedger.forward sourceEntry = newRevisedEntry
  sourceCurrentExact : HEq sourceVisit.current
    (crossCompilerCurrentStageAt depth).actionCurrent
  sourceEntryExact : HEq sourceEntry newRevisedEntry

namespace CrossCompilerRelationAppendStageAt

def exactSource {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :
    ExactTemporalCausalRootEventAt
      stage.sourceRoot.toAuthoritativeRoot.toLedgerRoot stage.sourceVisit :=
  stage.sourceRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt stage.sourceVisit

def targetPrior {depth : Nat}
    (_stage : CrossCompilerRelationAppendStageAt depth) :
    RootedAccountedUnfolding (CrossCompilerAtomAt (depth + 1)) :=
  (crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl

def targetAtom {depth : Nat}
    (_stage : CrossCompilerRelationAppendStageAt depth) :
    CrossCompilerAtomAt (depth + 1) :=
  .inr (crossCompilerCurrentStageAt depth).targetSeed

def targetRoot {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendLivingRoot stage.sourceRoot stage.exactSource.occurrence
    stage.targetPrior stage.targetAtom

def selectionVisit {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendTemporalVisitAt stage.sourceRoot stage.exactSource.occurrence
    stage.targetPrior stage.targetAtom 0

def actionVisit {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendTemporalVisitAt stage.sourceRoot stage.exactSource.occurrence
    stage.targetPrior stage.targetAtom 1

def selectionEntry {depth : Nat}
    (_stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendEntryAt 0

def actionEntry {depth : Nat}
    (_stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendEntryAt 1

def selectionAuthority {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendAuthorityAt stage.sourceRoot stage.exactSource.occurrence
    stage.targetPrior stage.targetAtom 0

def actionAuthority {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :=
  rootedAppendAuthorityAt stage.sourceRoot stage.exactSource.occurrence
    stage.targetPrior stage.targetAtom 1

theorem targetCurrent_exact {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :
    (crossCompilerCurrentStageAt depth).targetCurrent =
      rootedAppendedCurrent stage.targetPrior stage.targetAtom :=
  (crossCompilerCurrentStageAt depth).targetCurrentExact

theorem selectionCurrent_exact {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :
    HEq stage.selectionVisit.current
      (crossCompilerCurrentStageAt depth).targetCurrent := by
  exact (heq_of_eq (rootedAppendRootVisitAt_zero_current
    (sourceRoot := stage.sourceRoot)
    (sourceOccurrence := stage.exactSource.occurrence)
    (prior := stage.targetPrior) (nextAtom := stage.targetAtom))).trans
      (heq_of_eq stage.targetCurrent_exact.symm)

theorem actionCurrent_exact {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :
    HEq stage.actionVisit.current
      (crossCompilerCurrentStageAt (depth + 1)).actionCurrent := by
  exact (heq_of_eq (rootedAppendRootVisitAt_one_current
    (sourceRoot := stage.sourceRoot)
    (sourceOccurrence := stage.exactSource.occurrence)
    (prior := stage.targetPrior) (nextAtom := stage.targetAtom))).trans
      ((heq_of_eq (congrArg retainedCrossCompilerCurrentAt
        stage.targetCurrent_exact)).symm.trans
          (heq_of_eq
            (crossCompilerCurrentStageAt_succ_actionCurrent depth).symm))

private def next {depth : Nat}
    (stage : CrossCompilerRelationAppendStageAt depth) :
    CrossCompilerRelationAppendStageAt (depth + 1) where
  SourceV := RootedAppendVAt stage.targetPrior stage.targetAtom
  sourceRoot := stage.targetRoot
  sourceVisit := stage.actionVisit
  sourceEntry := stage.actionEntry
  sourceAuthority := stage.actionAuthority
  sourceLawSurfaceEq := rfl
  sourceOccurrenceUnique := by
    intro occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl old => exact nomatch event
    | inr direction => cases direction; cases event; rfl
  sourceSupportExact := rfl
  sourceInitialSupportHEq := HEq.rfl
  sourceInitialOpenLedger :=
    sequentialCriticalActionAppendIdentityTranslation.oldOpenLedger
      minimalCoface.cofaceSupport
  sourceInitialOpenLedgerHEq := HEq.rfl
  sourceInitialLedgerResponsibilityCommutes := fun _ => rfl
  sourceInitialLedgerClaimCommutes := fun _ => rfl
  sourceInitialLedgerBudgetConservative := fun _ => Nat.le_refl _
  sourceInitialLedgerNoFresh := fun targetEntry =>
    ⟨⟨targetEntry, PLift.up rfl⟩⟩
  sourceEntryTargetExact := rfl
  sourceCurrentExact := stage.actionCurrent_exact
  sourceEntryExact := HEq.rfl

end CrossCompilerRelationAppendStageAt

private def initialCrossCompilerRelationAppendStage :
    CrossCompilerRelationAppendStageAt 0 where
  SourceV := AppendVAt (stageAt 1).sourcePrior (stageAt 1).sourceCarrier
  sourceRoot := (stageAt 1).sourceRoot
  sourceVisit := (stageAt 1).actionVisit
  sourceEntry := criticalActionAppendEntryAt 1
  sourceAuthority := criticalActionAppendAuthorityAt
    (stageAt 1).predecessorRoot (stageAt 1).predecessorOccurrence
    (stageAt 1).sourcePrior (stageAt 1).sourceCarrier 1
  sourceLawSurfaceEq := rfl
  sourceOccurrenceUnique := by
    intro occurrence
    rcases occurrence with ⟨support, event⟩
    cases support with
    | inl old => exact nomatch event
    | inr direction => cases direction; cases event; rfl
  sourceSupportExact := rfl
  sourceInitialSupportHEq := HEq.rfl
  sourceInitialOpenLedger :=
    sequentialCriticalActionAppendIdentityTranslation.oldOpenLedger
      minimalCoface.cofaceSupport
  sourceInitialOpenLedgerHEq := HEq.rfl
  sourceInitialLedgerResponsibilityCommutes := fun _ => rfl
  sourceInitialLedgerClaimCommutes := fun _ => rfl
  sourceInitialLedgerBudgetConservative := fun _ => Nat.le_refl _
  sourceInitialLedgerNoFresh := fun targetEntry =>
    ⟨⟨targetEntry, PLift.up rfl⟩⟩
  sourceEntryTargetExact := rfl
  sourceCurrentExact := HEq.rfl
  sourceEntryExact := HEq.rfl

/-- Public producer accepts only depth.  The source of depth zero is the
installed stage-one relation occurrence after tick eight; every successor is
the previous target root's retained action visit. -/
def crossCompilerRelationAppendStageAt :
    (depth : Nat) → CrossCompilerRelationAppendStageAt depth
  | 0 => initialCrossCompilerRelationAppendStage
  | depth + 1 =>
      (crossCompilerRelationAppendStageAt depth).next

@[simp] theorem crossCompilerRelationAppendStageAt_zero_sourceRoot :
    (crossCompilerRelationAppendStageAt 0).sourceRoot =
      (stageAt 1).sourceRoot :=
  rfl

@[simp] theorem crossCompilerRelationAppendStageAt_succ_sourceRoot
    (depth : Nat) :
    (crossCompilerRelationAppendStageAt (depth + 1)).sourceRoot =
      (crossCompilerRelationAppendStageAt depth).targetRoot :=
  rfl

theorem crossCompilerRelationAppendStageAt_targetCurrent_exact
    (depth : Nat) :
    HEq (crossCompilerRelationAppendStageAt depth).selectionVisit.current
      (crossCompilerCurrentStageAt depth).targetCurrent :=
  (crossCompilerRelationAppendStageAt depth).selectionCurrent_exact

theorem crossCompilerRelationAppendStageAt_nextActionCurrent_exact
    (depth : Nat) :
    HEq (crossCompilerRelationAppendStageAt depth).actionVisit.current
      (crossCompilerCurrentStageAt (depth + 1)).actionCurrent :=
  (crossCompilerRelationAppendStageAt depth).actionCurrent_exact

theorem crossCompilerRelationAppendStageAt_sourceLineage_exact
    (depth : Nat) :
    (crossCompilerRelationAppendStageAt depth).SourceV.Lineage =
        (NewN.Lineage × Nat) ∧
      HEq
        ((crossCompilerRelationAppendStageAt depth).SourceV.lineageAt
          (crossCompilerRelationAppendStageAt depth).sourceVisit.current)
        (NewN.lineageAt minimalCoface.cofaceSupport,
          (crossCompilerCurrentStageAt depth).actionCurrent.trace.length) := by
  induction depth with
  | zero => exact ⟨rfl, HEq.rfl⟩
  | succ depth _inductionHypothesis =>
      refine ⟨rfl, ?_⟩
      have currentEq :
          (crossCompilerRelationAppendStageAt (depth + 1)
            ).sourceVisit.current =
            (crossCompilerCurrentStageAt (depth + 1)).actionCurrent :=
        eq_of_heq
          (crossCompilerRelationAppendStageAt (depth + 1)
            ).sourceCurrentExact
      rw [currentEq]
      change HEq
        (NewN.lineageAt minimalCoface.cofaceSupport,
          (crossCompilerCurrentStageAt (depth + 1)).actionCurrent.trace.length)
        (NewN.lineageAt minimalCoface.cofaceSupport,
          (crossCompilerCurrentStageAt (depth + 1)).actionCurrent.trace.length)
      exact HEq.rfl

theorem crossCompilerRelationAppendStageAt_directConsumer (depth : Nat) :
    ((crossCompilerRelationAppendStageAt depth).targetRoot
        ).toAuthoritativeRoot.toRoot.source.initial =
      (crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl ∧
    (rootedAppendFirstSuccessor
      (crossCompilerRelationAppendStageAt depth).targetPrior
      (crossCompilerRelationAppendStageAt depth).targetAtom).targetCurrent =
      (crossCompilerCurrentStageAt depth).targetCurrent ∧
    HEq (crossCompilerRelationAppendStageAt depth).selectionVisit.current
      (crossCompilerCurrentStageAt depth).targetCurrent ∧
    HEq (crossCompilerRelationAppendStageAt depth).actionVisit.current
      (crossCompilerCurrentStageAt (depth + 1)).actionCurrent := by
  refine ⟨rfl, ?_,
    crossCompilerRelationAppendStageAt_targetCurrent_exact depth,
    crossCompilerRelationAppendStageAt_nextActionCurrent_exact depth⟩
  exact (rootedAppendFirstSuccessor_target_exact
    (crossCompilerRelationAppendStageAt depth).targetPrior
    (crossCompilerRelationAppendStageAt depth).targetAtom).trans
      (crossCompilerRelationAppendStageAt depth).targetCurrent_exact.symm

end
end M14SourceGeneratedCrossCompilerRelationAppendStage
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendStage.crossCompilerRelationAppendStageAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendStage.crossCompilerRelationAppendStageAt_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendStage.crossCompilerRelationAppendStageAt_sourceLineage_exact
