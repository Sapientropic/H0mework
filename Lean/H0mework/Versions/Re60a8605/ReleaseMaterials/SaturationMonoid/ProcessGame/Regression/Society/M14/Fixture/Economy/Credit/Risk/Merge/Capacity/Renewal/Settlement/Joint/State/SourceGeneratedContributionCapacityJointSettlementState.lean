import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Action.SourceGeneratedSequentialContributionCapacityJointSettlement

/-!
# Inquiry states for joint survivor settlement

The survivor source state generates the actual representation-changing
action.  Its target state reads row `0` at the exact faithful-terminal current;
whole-ledger terminal authority remains in the compiler's complete `Fin 2`
patch and is not inferred from this source-fixed runtime query.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement

abbrev CanonicalContributionCapacityJointSettlementMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
    sourceIndex

abbrev CanonicalContributionCapacityJointSettlementActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  generatedContributionCapacityJointSettlementActionAt oldVisit sourceIndex
    (CanonicalContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex)

abbrev CanonicalContributionCapacityJointSettlementRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
    (CanonicalContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex)

def contributionCapacityJointSettlementActionStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStateAt (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  root := ContributionCapacityJointSettlementSurvivorRootAt oldVisit
    sourceIndex
  visit := contributionCapacityJointSettlementSurvivorVisitAt oldVisit
    sourceIndex
  U7 := contributionCapacityReopeningU7 oldVisit
  calculus := contributionCapacityReopeningCalculus oldVisit
  Query := Unit
  entryAt := fun _ =>
    contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex
  authorityAt := fun _ =>
    contributionCapacityJointSettlementActionAuthorityAt oldVisit sourceIndex
      (CanonicalContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex)
  compilationProgramAt := fun _ =>
    contributionCapacityJointSettlementActionCompilationProgramAt oldVisit
      sourceIndex
      (CanonicalContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex)
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacitySettlementSurvivorProjection.inquiry 0
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacityJointSettlementActionPresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStatePresentation where
  N := ReopeningNAt oldVisit
  V := ContributionCapacitySettlementSurvivorVAt oldVisit
  state := RootInquiryEngineStateAt.create
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex)

@[simp] theorem contributionCapacityJointSettlementActionState_compiles_generated
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementActionStateAt oldVisit sourceIndex
      ).compileInquiry () =
      .actualAction
        (CanonicalContributionCapacityJointSettlementActionAt oldVisit
          sourceIndex) :=
  rfl

def contributionCapacityJointSettlementTerminalInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ULift.up.{1, 0}
    ((CanonicalContributionCapacityJointSettlementRootAt oldVisit sourceIndex
      ).emitted
        (CanonicalContributionCapacityJointSettlementActionAt oldVisit
          sourceIndex).target.targetVisit.current)

def contributionCapacityJointSettlementTerminalAnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootSemanticFaceAt
      (CanonicalContributionCapacityJointSettlementRootAt oldVisit sourceIndex)
      (CanonicalContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex).target.targetVisit where
  projection := ContributionCapacityJointSettlementProjection.terminal 0
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacityJointSettlementTerminalAnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacityJointSettlementTerminalInquiryEventAt oldVisit
        sourceIndex)
      (CanonicalContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex).target.targetEntry
      (contributionCapacityJointSettlementTerminalAnswerFaceAt oldVisit
        sourceIndex) where
  projection := ContributionCapacityJointSettlementProjection.consumer 0
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacityJointSettlementTerminalCompilationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryCompilationAt
      (CanonicalContributionCapacityJointSettlementRootAt oldVisit sourceIndex)
      (CanonicalContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex).target.targetVisit
      (contributionCapacityJointSettlementU7 oldVisit)
      (contributionCapacityJointSettlementCalculus oldVisit)
      (contributionCapacityJointSettlementTheory oldVisit) ()
      (contributionCapacityJointSettlementTerminalInquiryEventAt oldVisit
        sourceIndex)
      (CanonicalContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex).target.targetEntry
      (CanonicalContributionCapacityJointSettlementActionAt oldVisit
        sourceIndex).target.targetAuthority :=
  .answered
    (contributionCapacityJointSettlementTerminalAnswerFaceAt oldVisit
      sourceIndex)
    (contributionCapacityJointSettlementTerminalAnswerConsumerAt oldVisit
      sourceIndex)

def contributionCapacityJointSettlementTerminalStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStateAt (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  root := CanonicalContributionCapacityJointSettlementRootAt oldVisit
    sourceIndex
  visit := (CanonicalContributionCapacityJointSettlementActionAt oldVisit
    sourceIndex).target.targetVisit
  U7 := contributionCapacityJointSettlementU7 oldVisit
  calculus := contributionCapacityJointSettlementCalculus oldVisit
  Query := Unit
  entryAt := fun _ =>
    (CanonicalContributionCapacityJointSettlementActionAt oldVisit
      sourceIndex).target.targetEntry
  authorityAt := fun _ =>
    (CanonicalContributionCapacityJointSettlementActionAt oldVisit
      sourceIndex).target.targetAuthority
  compilationProgramAt := fun _ =>
    { compile := fun _ =>
        contributionCapacityJointSettlementTerminalCompilationAt oldVisit
          sourceIndex }
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityJointSettlementProjection.inquiry 0
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacityJointSettlementTerminalPresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStatePresentation where
  N := JointSettlementNAt oldVisit
  V := ContributionCapacityJointSettlementVAt oldVisit
  state := RootInquiryEngineStateAt.create
    (contributionCapacityJointSettlementTerminalStateAt oldVisit sourceIndex)

@[simp] theorem contributionCapacityJointSettlementTerminalState_compiles_answered
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementTerminalStateAt oldVisit sourceIndex
      ).compileInquiry () =
      .answered
        (contributionCapacityJointSettlementTerminalAnswerFaceAt oldVisit
          sourceIndex)
        (contributionCapacityJointSettlementTerminalAnswerConsumerAt oldVisit
          sourceIndex) :=
  rfl

end
end M14SourceGeneratedContributionCapacityJointSettlementState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementState.contributionCapacityJointSettlementActionState_compiles_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementState.contributionCapacityJointSettlementTerminalState_compiles_answered
