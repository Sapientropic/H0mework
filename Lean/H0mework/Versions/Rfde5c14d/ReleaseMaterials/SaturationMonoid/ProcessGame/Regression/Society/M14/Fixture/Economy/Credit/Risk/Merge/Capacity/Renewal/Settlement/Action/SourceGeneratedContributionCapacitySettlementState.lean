import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedSequentialContributionCapacitySettlement

/-!
# Inquiry states for contribution-capacity settlement and handoff

The reopening source state compiles the exact settlement action.  Its target
state consumes the faithful-terminal answer at Bool current `true`.  The
generated handoff then enters the existing two-row survivor root and continues
with fresh answer/renewal occurrences.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedSequentialContributionCapacitySettlement

/-! ## Exact source action state -/

def contributionCapacitySettlementActionStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStateAt (ReopeningNAt oldVisit)
      (ReopeningVAt oldVisit sourceIndex) where
  root := ContributionCapacitySettlementActionRootAt oldVisit sourceIndex
  visit := contributionCapacitySettlementActionVisitAt oldVisit sourceIndex
  U7 := contributionCapacityReopeningU7 oldVisit
  calculus := contributionCapacityReopeningCalculus oldVisit
  Query := Unit
  entryAt := fun _ =>
    contributionCapacitySettlementActionEntryAt oldVisit sourceIndex
  authorityAt := fun _ =>
    contributionCapacitySettlementActionAuthorityAt oldVisit sourceIndex
  compilationProgramAt := fun _ =>
    contributionCapacitySettlementActionCompilationProgramAt oldVisit
      sourceIndex
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityReopeningProjection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacitySettlementActionPresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStatePresentation where
  N := ReopeningNAt oldVisit
  V := ReopeningVAt oldVisit sourceIndex
  state := RootInquiryEngineStateAt.create
    (contributionCapacitySettlementActionStateAt oldVisit sourceIndex)

@[simp] theorem contributionCapacitySettlementActionState_compiles_generated
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () =
      .actualAction
        (generatedContributionCapacitySettlementActionAt oldVisit
          sourceIndex) :=
  rfl

/-! ## Faithful-terminal target state -/

abbrev CanonicalContributionCapacitySettlementSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacitySettlementActionExactSourceEventAt oldVisit sourceIndex

abbrev CanonicalContributionCapacitySettlementRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacitySettlementRootAt oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
      sourceIndex)

abbrev CanonicalContributionCapacitySettlementActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  generatedContributionCapacitySettlementActionAt oldVisit sourceIndex

def contributionCapacitySettlementTerminalInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ULift.up.{1, 0}
    ((CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex)
      |>.emitted
        ((CanonicalContributionCapacitySettlementActionAt oldVisit
          sourceIndex).target.targetVisit.current))

def contributionCapacitySettlementTerminalAnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootSemanticFaceAt
      (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex)
      ((CanonicalContributionCapacitySettlementActionAt oldVisit
        sourceIndex).target.targetVisit) where
  projection := ContributionCapacitySettlementProjection.answer
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacitySettlementTerminalAnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacitySettlementTerminalInquiryEventAt oldVisit
        sourceIndex)
      ((CanonicalContributionCapacitySettlementActionAt oldVisit
        sourceIndex).target.targetEntry)
      (contributionCapacitySettlementTerminalAnswerFaceAt oldVisit
        sourceIndex) where
  projection := ContributionCapacitySettlementProjection.consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacitySettlementTerminalCompilationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryCompilationAt
      (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex)
      ((CanonicalContributionCapacitySettlementActionAt oldVisit
        sourceIndex).target.targetVisit)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacitySettlementTerminalInquiryEventAt oldVisit
        sourceIndex)
      ((CanonicalContributionCapacitySettlementActionAt oldVisit
        sourceIndex).target.targetEntry)
      ((CanonicalContributionCapacitySettlementActionAt oldVisit
        sourceIndex).target.targetAuthority) :=
  .answered
    (contributionCapacitySettlementTerminalAnswerFaceAt oldVisit sourceIndex)
    (contributionCapacitySettlementTerminalAnswerConsumerAt oldVisit
      sourceIndex)

def contributionCapacitySettlementTerminalStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStateAt (SettlementNAt oldVisit) (SettlementVAt oldVisit) where
  root := CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
  visit := (CanonicalContributionCapacitySettlementActionAt oldVisit
    sourceIndex).target.targetVisit
  U7 := contributionCapacityReopeningU7 oldVisit
  calculus := contributionCapacityReopeningCalculus oldVisit
  Query := Unit
  entryAt := fun _ =>
    (CanonicalContributionCapacitySettlementActionAt oldVisit
      sourceIndex).target.targetEntry
  authorityAt := fun _ =>
    (CanonicalContributionCapacitySettlementActionAt oldVisit
      sourceIndex).target.targetAuthority
  compilationProgramAt := fun _ =>
    { compile := fun _ =>
        contributionCapacitySettlementTerminalCompilationAt oldVisit
          sourceIndex }
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacitySettlementProjection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacitySettlementTerminalPresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStatePresentation where
  N := SettlementNAt oldVisit
  V := SettlementVAt oldVisit
  state := RootInquiryEngineStateAt.create
    (contributionCapacitySettlementTerminalStateAt oldVisit sourceIndex)

@[simp] theorem contributionCapacitySettlementTerminalState_compiles_answered
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementTerminalStateAt oldVisit sourceIndex
      ).compileInquiry () =
      .answered
        (contributionCapacitySettlementTerminalAnswerFaceAt oldVisit
          sourceIndex)
        (contributionCapacitySettlementTerminalAnswerConsumerAt oldVisit
          sourceIndex) :=
  rfl

/-! ## Generated two-row survivor states -/

abbrev CanonicalContributionCapacitySettlementSurvivorRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
      sourceIndex)

def contributionCapacitySettlementSurvivorRootVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nat → RootVisit
      (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
        sourceIndex).toAuthoritativeRoot.toRoot
  | 0 =>
      (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
        sourceIndex).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 =>
      (contributionCapacitySettlementSurvivorRootVisitAt oldVisit sourceIndex
        index).next rfl

def contributionCapacitySettlementSurvivorVisitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeTemporalVisitAt
      (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
        sourceIndex).toAuthoritativeRoot.toLedgerRoot :=
  .finite (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
    sourceIndex index)

@[simp] theorem contributionCapacitySettlementSurvivorRootVisit_depth
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
        (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
          sourceIndex index).history =
      index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        ProductiveFiniteRootHistoryAt.causalDepth
            (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
              sourceIndex index).history + 1 =
          index + 1
      rw [inductionHypothesis]

@[simp] theorem contributionCapacitySettlementSurvivorVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (show Nat from
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
        index).current) =
      contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
        index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
            sourceIndex index).current) + 1 =
          contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
            (index + 1)
      change
        (show Nat from
          (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
            sourceIndex index).current) =
          contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
            index at inductionHypothesis
      omega

def contributionCapacitySettlementSurvivorAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
          sourceIndex)
        (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          index)
        (contributionCapacitySettlementSurvivorContribution oldVisit)
  | 0 => contributionCapacitySettlementSurvivorInitialAuthority oldVisit
      sourceIndex
      (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
        sourceIndex)
  | index + 1 =>
      (contributionCapacitySettlementSurvivorAuthorityAt oldVisit sourceIndex
        index).next rfl

def contributionCapacitySettlementSurvivorInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ULift.up.{1, 0}
    ((CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
      sourceIndex).emitted
        (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          index).current)

def contributionCapacitySettlementSurvivorAnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
        sourceIndex)
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
        index) where
  projection := ContributionCapacitySettlementSurvivorProjection.answer 0
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacitySettlementSurvivorAnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacitySettlementSurvivorInquiryEventAt oldVisit
        sourceIndex index)
      (contributionCapacitySettlementSurvivorContribution oldVisit)
      (contributionCapacitySettlementSurvivorAnswerFaceAt oldVisit sourceIndex
        index) where
  projection := ContributionCapacitySettlementSurvivorProjection.consumer 0
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacitySettlementSurvivorCompilationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeInquiryCompilationAt
      (CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
        sourceIndex)
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
        index)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacitySettlementSurvivorInquiryEventAt oldVisit
        sourceIndex index)
      (contributionCapacitySettlementSurvivorContribution oldVisit)
      (contributionCapacitySettlementSurvivorAuthorityAt oldVisit sourceIndex
        index) :=
  .answered
    (contributionCapacitySettlementSurvivorAnswerFaceAt oldVisit sourceIndex
      index)
    (contributionCapacitySettlementSurvivorAnswerConsumerAt oldVisit
      sourceIndex index)

def contributionCapacitySettlementSurvivorStateAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    RootInquiryStateAt (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  root := CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
    sourceIndex
  visit := contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
    index
  U7 := contributionCapacityReopeningU7 oldVisit
  calculus := contributionCapacityReopeningCalculus oldVisit
  Query := Unit
  entryAt := fun _ =>
    contributionCapacitySettlementSurvivorContribution oldVisit
  authorityAt := fun _ =>
    contributionCapacitySettlementSurvivorAuthorityAt oldVisit sourceIndex
      index
  compilationProgramAt := fun _ =>
    { compile := fun _ => contributionCapacitySettlementSurvivorCompilationAt
        oldVisit sourceIndex index }
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacitySettlementSurvivorProjection.inquiry 0
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacitySettlementSurvivorPresentationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    RootInquiryStatePresentation where
  N := ReopeningNAt oldVisit
  V := ContributionCapacitySettlementSurvivorVAt oldVisit
  state := RootInquiryEngineStateAt.create
    (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex index)

@[simp] theorem contributionCapacitySettlementSurvivorState_compiles_answered
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacitySettlementSurvivorStateAt oldVisit sourceIndex index
      ).compileInquiry () =
      .answered
        (contributionCapacitySettlementSurvivorAnswerFaceAt oldVisit
          sourceIndex index)
        (contributionCapacitySettlementSurvivorAnswerConsumerAt oldVisit
          sourceIndex index) :=
  rfl

end
end M14SourceGeneratedContributionCapacitySettlementState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementState.contributionCapacitySettlementActionState_compiles_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementState.contributionCapacitySettlementTerminalState_compiles_answered
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementState.contributionCapacitySettlementSurvivorState_compiles_answered
