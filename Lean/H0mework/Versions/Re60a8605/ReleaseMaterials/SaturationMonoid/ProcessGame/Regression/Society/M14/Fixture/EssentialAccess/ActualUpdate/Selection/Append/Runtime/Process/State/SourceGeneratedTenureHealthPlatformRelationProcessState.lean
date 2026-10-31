import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.Runtime.SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.SourceGeneratedTenureQueueAppendContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.Continuation.SourceGeneratedHealthQueueAppendContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Platform.Continuation.SourceGeneratedPlatformQueueAppendContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendPresentation
import H0mework.Foundation.Runtime.Inquiry

/-!
# Canonical U8-to-cross-compiler recurrence process state

This module owns the state grammar, exact presentations and causal lineage
ranks.  A one-step homogeneous bootstrap hands control to the heterogeneous
cross-compiler recurrence; no terminal tail or event schedule is installed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureQueueAppendRuntime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M10OccurrenceCapacityProcessFixture
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Compilation
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedCriticalEventSelectionRevisedContinuation
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedSequentialTenureQueueAppend
open M14SourceGeneratedQueueAppendContinuation
open M14SourceGeneratedCriticalActionAppendContinuation
open M14SourceGeneratedRootedAccountedUnfoldingAppendContinuation
open M14SourceGeneratedTenureQueueAppendContinuation
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedHealthQueueAppendContinuation
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedPlatformQueueAppendTarget
open M14SourceGeneratedSequentialPlatformQueueAppend
open M14SourceGeneratedPlatformQueueAppendContinuation
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrencePresentation
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendPresentation

def revisedTenureActionInquiryState : RootInquiryStateAt NewN NewV where
  root := revisedLivingRoot
  visit := revisedSelectionTemporalVisitAt 2
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => tenureAppendSource.sourceEntry
  authorityAt := fun _ => tenureAppendSource.sourceAuthority
  compilationProgramAt := fun _ =>
    { compile := fun _ => tenureQueueAppendActualActionCompilation }
  compilationFaceAt := fun _ =>
    { projection := revisedInquiryProjection
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def revisedTenureActionPresentation : RootInquiryStatePresentation where
  N := NewN
  V := NewV
  state := RootInquiryEngineStateAt.create revisedTenureActionInquiryState

def tenureHealthActionInquiryState : RootInquiryStateAt NewN
    (AppendVAt tenureAppendPrior tenureQueueAction) where
  root := tenureAppendTargetRoot
  visit := tenureAppendTemporalVisitAt 1
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => sourceGeneratedHealthQueueActionAtTenureRoot.sourceEntry
  authorityAt := fun _ =>
    sourceGeneratedHealthQueueActionAtTenureRoot.sourceAuthority
  compilationProgramAt := fun _ =>
    { compile := fun _ => healthQueueAppendActualActionCompilation }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def tenureHealthActionPresentation : RootInquiryStatePresentation where
  N := NewN
  V := AppendVAt tenureAppendPrior tenureQueueAction
  state := RootInquiryEngineStateAt.create tenureHealthActionInquiryState

def healthPlatformActionInquiryState : RootInquiryStateAt NewN
    (AppendVAt healthAppendPrior healthQueueAction) where
  root := healthAppendTargetRoot
  visit := healthAppendTemporalVisitAt 1
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => sourceGeneratedPlatformQueueActionAtHealthRoot.sourceEntry
  authorityAt := fun _ =>
    sourceGeneratedPlatformQueueActionAtHealthRoot.sourceAuthority
  compilationProgramAt := fun _ =>
    { compile := fun _ => platformQueueAppendActualActionCompilation }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def healthPlatformActionPresentation : RootInquiryStatePresentation where
  N := NewN
  V := AppendVAt healthAppendPrior healthQueueAction
  state := RootInquiryEngineStateAt.create healthPlatformActionInquiryState

inductive ProcessState
  | oldU8
  | tenureAction
  | tenureSelection
  | healthAction
  | healthSelection
  | platformAction
  | platformSelection
  | relationAction (index : Fin 1)
  | relationSelection (index : Fin 1)
  | crossAction (depth : Nat)
  | crossSelection (depth : Nat)
  deriving DecidableEq

def processPresentation : ProcessState → RootInquiryStatePresentation
  | .oldU8 => healthTargetSelectionPresentation
  | .tenureAction => revisedTenureActionPresentation
  | .tenureSelection => tenureAppendSelectionPresentationAt 0
  | .healthAction => tenureHealthActionPresentation
  | .healthSelection => healthAppendPresentationAt 0
  | .platformAction => healthPlatformActionPresentation
  | .platformSelection => (stageAt 0).selectionPresentation
  | .relationAction index => actionPresentation (stageAt index.val)
  | .relationSelection index => (stageAt (index.val + 1)).selectionPresentation
  | .crossAction depth => crossCompilerActionPresentationAt depth
  | .crossSelection depth => crossCompilerSelectionPresentationAt depth

def erasedCurrentLabel (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun Carrier : Type => Carrier :=
  ⟨erased.current.V.Current, erased.current.visit.current⟩

def erasedLineageLabel (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun Lineage : Type => Lineage :=
  ⟨erased.current.V.Lineage,
    erased.current.V.lineageAt erased.current.visit.current⟩

theorem healthTargetOldSupport_card :
    Nat.card M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime.N.Support =
      2 := by
  change Nat.card Bool = 2
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_bool

set_option linter.style.haveILetI false in
theorem revisedSelectionSupport_card : Nat.card NewN.Support = 3 := by
  letI : Subsingleton (GeneratedDirectionAt RootedFailure) :=
    ⟨by
      intro left right
      cases left
      cases right
      rfl⟩
  letI : Finite (GeneratedDirectionAt RootedFailure) :=
    Finite.of_injective
      (fun _ : GeneratedDirectionAt RootedFailure => PUnit.unit)
      (by
        intro left right _
        cases left
        cases right
        rfl)
  letI : Nonempty (GeneratedDirectionAt RootedFailure) := ⟨.completion⟩
  have direction_card : Nat.card (GeneratedDirectionAt RootedFailure) = 1 :=
    Nat.card_unique
  change Nat.card
    (M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime.N.Support ⊕
      GeneratedDirectionAt RootedFailure) = 3
  rw [Nat.card_sum, healthTargetOldSupport_card, direction_card]

theorem healthTargetOldSupport_ne_revisedSelectionSupport :
    M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime.N.Support ≠
      NewN.Support := by
  intro equality
  have cards := congrArg Nat.card equality
  rw [healthTargetOldSupport_card, revisedSelectionSupport_card] at cards
  omega

def processAtom : ProcessState → Type
  | .crossAction depth => CrossCompilerAtomAt depth
  | .crossSelection depth => CrossCompilerAtomAt (depth + 1)
  | _ => CrossCompilerAtomAt 0

def processCurrent : (state : ProcessState) →
    RootedAccountedUnfolding (processAtom state)
  | .oldU8 | .tenureAction => tenureAppendPrior
  | .tenureSelection =>
      appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction
  | .healthAction => healthAppendPrior
  | .healthSelection =>
      appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction
  | .platformAction => platformAppendPrior
  | .platformSelection => (stageAt 0).selectionVisit.current
  | .relationAction index => (stageAt index.val).actionCurrent
  | .relationSelection index =>
      (stageAt (index.val + 1)).selectionVisit.current
  | .crossAction depth => (crossCompilerCurrentStageAt depth).actionCurrent
  | .crossSelection depth => (crossCompilerCurrentStageAt depth).targetCurrent

def processRank : ProcessState → Nat
  | .oldU8 | .tenureAction => 0
  | .tenureSelection => 1
  | .healthAction => 2
  | .healthSelection => 3
  | .platformAction => 4
  | .platformSelection => 5
  | .relationAction index => 6 + 2 * index.val
  | .relationSelection index => 7 + 2 * index.val
  | .crossAction depth => 8 + 2 * depth
  | .crossSelection depth => 9 + 2 * depth

def processExpectedCurrentLabel (state : ProcessState) :
    Sigma fun Carrier : Type => Carrier :=
  if state = .oldU8 then
    erasedCurrentLabel (processPresentation .oldU8).erase
  else
    ⟨RootedAccountedUnfolding (processAtom state), processCurrent state⟩

theorem processPresentation_currentLabel_exact (state : ProcessState) :
    erasedCurrentLabel (processPresentation state).erase =
      processExpectedCurrentLabel state := by
  cases state with
  | oldU8 => simp [processExpectedCurrentLabel]
  | tenureAction =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      rfl
  | tenureSelection =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact heq_of_eq tenureAppendRootVisitAt_zero_current
  | healthAction =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact heq_of_eq healthAppendPrior_exact
  | healthSelection =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact HEq.rfl
  | platformAction =>
      simp only [processExpectedCurrentLabel, reduceCtorEq, ↓reduceIte]
      rfl
  | platformSelection =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact HEq.rfl
  | relationAction index =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        processAtom,
        erasedCurrentLabel, RootInquiryStatePresentation.erase,
        actionPresentation_current_exact]
      refine Sigma.ext rfl ?_
      exact HEq.rfl
  | relationSelection index =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        processAtom,
        erasedCurrentLabel, RootInquiryStatePresentation.erase]
      refine Sigma.ext rfl ?_
      exact HEq.rfl
  | crossAction depth =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        processAtom, erasedCurrentLabel, RootInquiryStatePresentation.erase]
      exact type_eq_of_heq
        (crossCompilerActionPresentation_current_exact depth)
  | crossSelection depth =>
      simp [processExpectedCurrentLabel, processPresentation, processCurrent,
        processAtom, erasedCurrentLabel, RootInquiryStatePresentation.erase]
      let currentExact :=
        (crossCompilerPresentation_directConsumer depth).2.2.2.2
      exact ⟨type_eq_of_heq currentExact, currentExact⟩

theorem retainedSelectionNext_traceLength
    (current : EssentialAccessCriticalSelectionCurrent) :
    (retainedSelectionNext current).trace.length = current.trace.length + 1 := by
  unfold retainedSelectionNext RootedAccountedUnfolding.trace
    AccountedBranches.singleton
  simp

theorem appendedCriticalSelectionCurrent_traceLength
    (prior : EssentialAccessCriticalSelectionCurrent)
    (actionCarrier : SourceGeneratedEssentialAccessCriticalActionCarrier) :
    (appendedCriticalSelectionCurrent prior actionCarrier).trace.length =
      prior.trace.length + 1 := by
  unfold appendedCriticalSelectionCurrent RootedAccountedUnfolding.trace
    AccountedBranches.singleton
  simp

theorem healthAppendPrior_traceLength :
    healthAppendPrior.trace.length = tenureAppendPrior.trace.length + 2 := by
  rw [healthAppendPrior_exact, retainedSelectionNext_traceLength,
    appendedCriticalSelectionCurrent_traceLength]

theorem platformAppendPrior_traceLength :
    platformAppendPrior.trace.length = tenureAppendPrior.trace.length + 4 := by
  rw [platformAppendPrior_exact, retainedSelectionNext_traceLength,
    appendedCriticalSelectionCurrent_traceLength,
    healthAppendPrior_traceLength]

theorem initialRelationSelectionCurrent_traceLength :
    (stageAt 0).selectionVisit.current.trace.length =
      tenureAppendPrior.trace.length + 5 := by
  rw [(stageAt 0).selectionCurrent_exact,
    appendedCriticalSelectionCurrent_traceLength]
  change platformAppendPrior.trace.length + 1 = _
  rw [platformAppendPrior_traceLength]

theorem stageAt_actionCurrent_traceLength (depth : Nat) :
    (stageAt depth).actionCurrent.trace.length =
      tenureAppendPrior.trace.length + (6 + 2 * depth) := by
  induction depth with
  | zero =>
      rw [(stageAt 0).actionCurrent_exact,
        retainedSelectionNext_traceLength,
        appendedCriticalSelectionCurrent_traceLength]
      change platformAppendPrior.trace.length + 1 + 1 = _
      rw [platformAppendPrior_traceLength]
  | succ depth inductionHypothesis =>
      rw [stageAt_succ, RelationLineageRecurrenceStage.next_actionCurrent_exact,
        retainedSelectionNext_traceLength,
        appendedCriticalSelectionCurrent_traceLength,
        inductionHypothesis]
      omega

theorem stageAt_nextSelectionCurrent_traceLength (depth : Nat) :
    (stageAt (depth + 1)).selectionVisit.current.trace.length =
      tenureAppendPrior.trace.length + (7 + 2 * depth) := by
  rw [stageAt_succ, RelationLineageRecurrenceStage.selectionCurrent_exact,
    appendedCriticalSelectionCurrent_traceLength]
  change (stageAt depth).actionCurrent.trace.length + 1 = _
  rw [stageAt_actionCurrent_traceLength]
  omega

mutual

theorem rootedMap_traceLength {Source Target : Type}
    (transform : Source → Target)
    (current : RootedAccountedUnfolding Source) :
    (current.map transform).trace.length = current.trace.length := by
  cases current with
  | occur root branches =>
      change
        (transform root :: RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.mapBranches transform branches)).length =
        (root :: RootedAccountedUnfolding.traceBranches branches).length
      simp only [List.length_cons]
      exact congrArg Nat.succ
        (rootedMapBranches_traceLength transform branches)

theorem rootedMapBranches_traceLength {Source Target : Type}
    (transform : Source → Target)
    (branches : AccountedBranches Source) :
    (RootedAccountedUnfolding.mapBranches transform branches
      |> RootedAccountedUnfolding.traceBranches).length =
      (RootedAccountedUnfolding.traceBranches branches).length := by
  cases branches with
  | nil => rfl
  | cons head tail =>
      change
        ((head.map transform).trace ++
          RootedAccountedUnfolding.traceBranches
            (RootedAccountedUnfolding.mapBranches transform tail)).length =
        (head.trace ++ RootedAccountedUnfolding.traceBranches tail).length
      rw [List.length_append, List.length_append,
        rootedMap_traceLength, rootedMapBranches_traceLength]

end

theorem retainedCrossCompilerCurrent_traceLength {depth : Nat}
    (current : RootedAccountedUnfolding (CrossCompilerAtomAt depth)) :
    (retainedCrossCompilerCurrentAt current).trace.length =
      current.trace.length + 1 := by
  unfold retainedCrossCompilerCurrentAt RootedAccountedUnfolding.trace
    AccountedBranches.singleton
  simp

theorem crossCompilerTargetCurrent_traceLength (depth : Nat) :
    (crossCompilerCurrentStageAt depth).targetCurrent.trace.length =
      (crossCompilerCurrentStageAt depth).actionCurrent.trace.length + 1 := by
  rw [(crossCompilerCurrentStageAt depth).targetCurrentExact]
  change
    (RootedAccountedUnfolding.occur
      (Sum.inr (crossCompilerCurrentStageAt depth).targetSeed)
      (AccountedBranches.singleton
        ((crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl)) :
      RootedAccountedUnfolding
        (CrossCompilerAtomAt depth ⊕
          M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.ExactRelationSeed)
    ).trace.length =
      (crossCompilerCurrentStageAt depth).actionCurrent.trace.length + 1
  calc
    _ = ((crossCompilerCurrentStageAt depth).actionCurrent.map
          Sum.inl).trace.length + 1 := by
      unfold RootedAccountedUnfolding.trace AccountedBranches.singleton
      simp
      rfl
    _ = (crossCompilerCurrentStageAt depth).actionCurrent.trace.length + 1 := by
      rw [rootedMap_traceLength]

theorem crossCompilerActionCurrent_traceLength (depth : Nat) :
    (crossCompilerCurrentStageAt depth).actionCurrent.trace.length =
      tenureAppendPrior.trace.length + (8 + 2 * depth) := by
  induction depth with
  | zero =>
      change (stageAt 1).actionCurrent.trace.length =
        tenureAppendPrior.trace.length + (8 + 2 * 0)
      simpa using stageAt_actionCurrent_traceLength 1
  | succ depth inductionHypothesis =>
      rw [crossCompilerCurrentStageAt_succ_actionCurrent,
        retainedCrossCompilerCurrent_traceLength,
        crossCompilerTargetCurrent_traceLength, inductionHypothesis]
      omega

theorem crossCompilerSelectionCurrent_traceLength (depth : Nat) :
    (crossCompilerCurrentStageAt depth).targetCurrent.trace.length =
      tenureAppendPrior.trace.length + (9 + 2 * depth) := by
  rw [crossCompilerTargetCurrent_traceLength,
    crossCompilerActionCurrent_traceLength]
  omega

theorem processCurrent_traceLength (state : ProcessState) :
    (processCurrent state).trace.length =
      tenureAppendPrior.trace.length + processRank state := by
  cases state with
  | oldU8 | tenureAction => rfl
  | tenureSelection =>
      exact appendedCriticalSelectionCurrent_traceLength _ _
  | healthAction => exact healthAppendPrior_traceLength
  | healthSelection =>
      change
        (appendedCriticalSelectionCurrent healthAppendPrior
          (criticalActionCarrierOfQueueAction healthQueueAction)).trace.length =
        tenureAppendPrior.trace.length + 3
      rw [appendedCriticalSelectionCurrent_traceLength,
        healthAppendPrior_traceLength]
  | platformAction => exact platformAppendPrior_traceLength
  | platformSelection => exact initialRelationSelectionCurrent_traceLength
  | relationAction index => exact stageAt_actionCurrent_traceLength index.val
  | relationSelection index =>
      exact stageAt_nextSelectionCurrent_traceLength index.val
  | crossAction depth => exact crossCompilerActionCurrent_traceLength depth
  | crossSelection depth =>
      exact crossCompilerSelectionCurrent_traceLength depth

def processExpectedLineageLabel (state : ProcessState) :
    Sigma fun Lineage : Type => Lineage :=
  if state = .oldU8 then
    erasedLineageLabel (processPresentation .oldU8).erase
  else
    ⟨NewN.Lineage × Nat,
      (NewN.lineageAt minimalCoface.cofaceSupport,
        tenureAppendPrior.trace.length + processRank state)⟩

end
end M14SourceGeneratedTenureQueueAppendRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime.stageAt_actionCurrent_traceLength
