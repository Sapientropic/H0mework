import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.SourceGeneratedEssentialAccessCriticalActionAppendRoot
import H0mework.Foundation.Cofinal.ProductiveHistory

/-!
# Carrier-native critical-action append continuation

Every append generated from an already source-owned action carrier exposes the
same temporal spine.  The first visit is the appended current and subsequent
visits retain it.  Only `Fin 1` exposes the selection answer; a retained visit
can therefore host a separately source-sealed next action without a sibling
answered authority.  The `Nat` index is a visit spine, never an event schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalActionAppendContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot

section

variable {SourceV : ConstructiveRoot.Vocabulary}
variable (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
variable {sourceCurrent : SourceV.Current}
variable (sourceOccurrence :
  sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    sourceCurrent)
variable (prior : EssentialAccessCriticalSelectionCurrent)
variable (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier)

abbrev criticalActionAppendTargetRoot :=
  appendLivingRoot sourceRoot sourceOccurrence prior actionCarrier

def criticalActionAppendRootVisitAt : Nat →
    RootVisit (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
      actionCarrier).toAuthoritativeRoot.toRoot
  | 0 => (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
      actionCarrier).toAuthoritativeRoot.toRoot.initialVisit.next rfl
  | depth + 1 => (criticalActionAppendRootVisitAt depth).next rfl

def criticalActionAppendTemporalVisitAt (depth : Nat) :
    SourceNativeTemporalVisitAt
      (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier).toAuthoritativeRoot.toLedgerRoot :=
  .finite (criticalActionAppendRootVisitAt (sourceRoot := sourceRoot)
    (sourceOccurrence := sourceOccurrence) (prior := prior)
    (actionCarrier := actionCarrier) depth)

theorem criticalActionAppendNextEqAt (depth : Nat) :
    ((criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
      actionCarrier).toAuthoritativeRoot.toRoot.evolutionAt
        (criticalActionAppendRootVisitAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (actionCarrier := actionCarrier) depth).current).nextCurrent? =
      some (criticalActionAppendRootVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) (depth + 1)).current :=
  rfl

@[simp] theorem criticalActionAppendTemporalVisit_next_eq (depth : Nat) :
    (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier) depth).next
        (criticalActionAppendNextEqAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (actionCarrier := actionCarrier) depth) =
      criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) (depth + 1) :=
  rfl

@[simp] theorem criticalActionAppendRootVisitAt_zero_current :
    (criticalActionAppendRootVisitAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier) 0).current =
        appendedCriticalSelectionCurrent prior actionCarrier :=
  appendNativeTarget_initial prior actionCarrier

def criticalActionAppendEntryAt (_depth : Nat) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  newRevisedEntry

def criticalActionAppendInitialGenerated :=
  (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
    actionCarrier).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier).toAuthoritativeRoot.toRoot.initialVisit)

def criticalActionAppendInitialEntryRow :
    (criticalActionAppendInitialGenerated (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier)).GeneratedEntryRowAt newRevisedEntry :=
  ((criticalActionAppendInitialGenerated (sourceRoot := sourceRoot)
    (sourceOccurrence := sourceOccurrence) (prior := prior)
    (actionCarrier := actionCarrier)).canonicalGeneratedEntryRow?
      newRevisedEntry).get (by rfl)

def criticalActionAppendInitialAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier)
      (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) 0)
      (criticalActionAppendEntryAt 0) :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
      actionCarrier)
    newRevisedEntry
    (criticalActionAppendInitialEntryRow (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier))).next rfl

def criticalActionAppendAuthorityAt : (depth : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier)
      (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) depth)
      (criticalActionAppendEntryAt depth)
  | 0 => criticalActionAppendInitialAuthority (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier)
  | depth + 1 =>
      (criticalActionAppendAuthorityAt depth).next
        (criticalActionAppendNextEqAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (actionCarrier := actionCarrier) depth)

def criticalActionAppendAnswerFaceAt (selection : Fin 1) :
    SourceNativeRootSemanticFaceAt
      (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier)
      (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) selection.val) where
  projection := .answer
  active := PUnit.unit
  classifier_eq := rfl

def criticalActionAppendAnswerConsumerAt (selection : Fin 1) :
    SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        ((criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
          actionCarrier).emitted
            (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
              (sourceOccurrence := sourceOccurrence) (prior := prior)
              (actionCarrier := actionCarrier) selection.val).current))
      (criticalActionAppendEntryAt selection.val)
      (criticalActionAppendAnswerFaceAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) selection) where
  projection := .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def criticalActionAppendAnsweredCompilationAt (selection : Fin 1) :
    SourceNativeInquiryCompilationAt
      (criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
        actionCarrier)
      (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) selection.val)
      revisedInquiryU7 revisedInquiryCalculus revisedInquiryTheory ()
      (ULift.up.{1, 0}
        ((criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
          actionCarrier).emitted
            (criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
              (sourceOccurrence := sourceOccurrence) (prior := prior)
              (actionCarrier := actionCarrier) selection.val).current))
      (criticalActionAppendEntryAt selection.val)
      (criticalActionAppendAuthorityAt (sourceRoot := sourceRoot)
        (sourceOccurrence := sourceOccurrence) (prior := prior)
        (actionCarrier := actionCarrier) selection.val) :=
  .answered (criticalActionAppendAnswerFaceAt (sourceRoot := sourceRoot)
    (sourceOccurrence := sourceOccurrence) (prior := prior)
    (actionCarrier := actionCarrier) selection)
    (criticalActionAppendAnswerConsumerAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier) selection)

def criticalActionAppendInquiryStateAt (selection : Fin 1) :
    RootInquiryStateAt NewN (AppendVAt prior actionCarrier) where
  root := criticalActionAppendTargetRoot sourceRoot sourceOccurrence prior
    actionCarrier
  visit := criticalActionAppendTemporalVisitAt (sourceRoot := sourceRoot)
    (sourceOccurrence := sourceOccurrence) (prior := prior)
    (actionCarrier := actionCarrier) selection.val
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => criticalActionAppendEntryAt selection.val
  authorityAt := fun _ => criticalActionAppendAuthorityAt
    (sourceRoot := sourceRoot) (sourceOccurrence := sourceOccurrence)
    (prior := prior) (actionCarrier := actionCarrier) selection.val
  compilationProgramAt := fun _ =>
    { compile := fun _ => criticalActionAppendAnsweredCompilationAt
        (sourceRoot := sourceRoot) (sourceOccurrence := sourceOccurrence)
        (prior := prior) (actionCarrier := actionCarrier) selection }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def criticalActionAppendPresentationAt (selection : Fin 1) :
    RootInquiryStatePresentation where
  N := NewN
  V := AppendVAt prior actionCarrier
  state := RootInquiryEngineStateAt.create
    (criticalActionAppendInquiryStateAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier) selection)

theorem criticalActionAppendContinuation_directConsumer (selection : Fin 1) :
    (criticalActionAppendInquiryStateAt (sourceRoot := sourceRoot)
      (sourceOccurrence := sourceOccurrence) (prior := prior)
      (actionCarrier := actionCarrier) selection).compileInquiry () =
      SourceNativeInquiryCompilationAt.answered
        (criticalActionAppendAnswerFaceAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (actionCarrier := actionCarrier) selection)
        (criticalActionAppendAnswerConsumerAt (sourceRoot := sourceRoot)
          (sourceOccurrence := sourceOccurrence) (prior := prior)
          (actionCarrier := actionCarrier) selection) :=
  rfl

end
end
end M14SourceGeneratedCriticalActionAppendContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalActionAppendContinuation.criticalActionAppendAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalActionAppendContinuation.criticalActionAppendInquiryStateAt
