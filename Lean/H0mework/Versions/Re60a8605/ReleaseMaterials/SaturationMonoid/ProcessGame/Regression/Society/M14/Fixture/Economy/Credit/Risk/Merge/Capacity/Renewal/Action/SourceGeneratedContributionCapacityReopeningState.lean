import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedSequentialContributionCapacityReopening

/-!
# Capacity reopening source and target inquiry states

The source state replaces the revised root's index-one ordinary answer by the
exact sequential reopening action.  The action-generated root then follows
its transported residual row and answers at every generated successor visit.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningResidualCarry
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14UBIPeriodicActualServiceCapacity

/-! ## Source action state -/

def contributionCapacityReopeningActionStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStateAt (CapacityU8NAt oldVisit) (CapacityU8VAt oldVisit) where
  root := CapacityU8RootAt oldVisit
  visit := contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex
  U7 := contributionCapacityRevisedU7 oldVisit
  calculus := contributionCapacityRevisedCalculus oldVisit
  Query := Unit
  entryAt := fun _ => contributionCapacityU8GeneratedResidual oldVisit
  authorityAt := fun _ => contributionCapacityU8RuntimeAuthorityAt oldVisit
    sourceIndex
  compilationProgramAt := fun _ =>
    contributionCapacityReopeningActionCompilationProgramAt oldVisit sourceIndex
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityU8Projection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacityReopeningActionEngineStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  RootInquiryEngineStateAt.create
    (contributionCapacityReopeningActionStateAt oldVisit sourceIndex)

def contributionCapacityReopeningActionPresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootInquiryStatePresentation where
  N := CapacityU8NAt oldVisit
  V := CapacityU8VAt oldVisit
  state := contributionCapacityReopeningActionEngineStateAt oldVisit sourceIndex

@[simp] theorem contributionCapacityReopeningActionState_compiles_generated
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityReopeningActionStateAt oldVisit sourceIndex).compileInquiry () =
      .actualAction
        (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex) :=
  rfl

/-! ## Action-generated target states -/

abbrev CanonicalReopeningSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex

abbrev CanonicalReopeningRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ReopeningRootAt oldVisit sourceIndex
    (CanonicalReopeningSourceEventAt oldVisit sourceIndex)

abbrev CanonicalReopeningRootVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  RootVisit
    (CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot

def contributionCapacityReopeningRootVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nat → CanonicalReopeningRootVisitAt oldVisit sourceIndex
  | 0 => (CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot
      |>.toRoot.initialVisit
  | index + 1 =>
      (contributionCapacityReopeningRootVisitAt oldVisit sourceIndex index).next
        rfl

def contributionCapacityReopeningTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeTemporalVisitAt
      ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toLedgerRoot) :=
  .finite (contributionCapacityReopeningRootVisitAt oldVisit sourceIndex index)

@[simp] theorem contributionCapacityReopeningVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (show Nat from
      (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex index).current) = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (contributionCapacityReopeningRootVisitAt oldVisit sourceIndex index).current) + 1 = index + 1
      exact congrArg (fun current : Nat => current + 1) inductionHypothesis

/-- Every actual current of the action-generated root receives its own
period-indexed UBI renewal projection.  No current reuses a completed renewal
from an earlier current. -/
def contributionCapacityReopeningRenewalFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (CanonicalReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
        index) where
  projection := ContributionCapacityReopeningProjection.renewal
  active := PUnit.unit
  classifier_eq := rfl

theorem contributionCapacityReopeningRootGeneratedRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAtCurrent sourceIndex index)) := by
  have generated :=
    (contributionCapacityReopeningRenewalFaceAt oldVisit sourceIndex index)
      |>.rootRead.down
  simpa only [contributionCapacityReopeningVisit_current_exact] using generated

theorem contributionCapacityReopeningNextEqAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot.evolutionAt
      (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex index).current).nextCurrent? =
      some
        (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
          (index + 1)).current :=
  rfl

def contributionCapacityReopeningInitialResidualAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CanonicalReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex 0)
      (contributionCapacityReopeningInitialResidual oldVisit) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (CanonicalReopeningRootAt oldVisit sourceIndex)
    (contributionCapacityReopeningInitialResidual oldVisit)
    (contributionCapacityReopeningInitialResidualRow oldVisit sourceIndex
      (CanonicalReopeningSourceEventAt oldVisit sourceIndex))

theorem contributionCapacityReopeningInitialResidualNextEntry_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (next_eq :
      ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot.evolutionAt
        (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex 0).current).nextCurrent? =
        some
          (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
            1).current) :
    ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
          next_eq
          (contributionCapacityReopeningInitialResidual oldVisit)) =
      contributionCapacityReopeningTargetResidual oldVisit := by
  rfl

theorem contributionCapacityReopeningTargetResidualNextEntry_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (next_eq :
      ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot.evolutionAt
        (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
          (index + 1)).current).nextCurrent? =
        some
          (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
            (index + 2)).current) :
    ((CanonicalReopeningRootAt oldVisit sourceIndex).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
          next_eq (contributionCapacityReopeningTargetResidual oldVisit)) =
      contributionCapacityReopeningTargetResidual oldVisit := by
  rfl

def contributionCapacityReopeningResidualAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CanonicalReopeningRootAt oldVisit sourceIndex)
        (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex index)
        (match index with
          | 0 => contributionCapacityReopeningInitialResidual oldVisit
          | _ + 1 => contributionCapacityReopeningTargetResidual oldVisit)
  | 0 => contributionCapacityReopeningInitialResidualAuthorityAt oldVisit
      sourceIndex
  | index + 1 => by
      cases index with
      | zero =>
          let next_eq := contributionCapacityReopeningNextEqAt oldVisit
            sourceIndex 0
          have advanced :=
            (contributionCapacityReopeningInitialResidualAuthorityAt oldVisit
              sourceIndex).next next_eq
          have entry_eq :=
            contributionCapacityReopeningInitialResidualNextEntry_exact
              oldVisit sourceIndex next_eq
          exact Eq.mp
            (congrArg
              (fun entry => SourceNativeLivingTemporalCausalEntryAuthorityAt
                (CanonicalReopeningRootAt oldVisit sourceIndex)
                ((contributionCapacityReopeningTemporalVisitAt oldVisit
                  sourceIndex 0).next next_eq) entry)
              entry_eq)
            advanced
      | succ index =>
          have previous := contributionCapacityReopeningResidualAuthorityAt
            oldVisit sourceIndex (index + 1)
          change SourceNativeLivingTemporalCausalEntryAuthorityAt
            (CanonicalReopeningRootAt oldVisit sourceIndex)
            (contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex
              (index + 1))
            (contributionCapacityReopeningTargetResidual oldVisit) at previous
          let next_eq := contributionCapacityReopeningNextEqAt oldVisit
            sourceIndex (index + 1)
          have advanced := previous.next next_eq
          have entry_eq :=
            contributionCapacityReopeningTargetResidualNextEntry_exact
              oldVisit sourceIndex index next_eq
          exact Eq.mp
            (congrArg
              (fun entry => SourceNativeLivingTemporalCausalEntryAuthorityAt
                (CanonicalReopeningRootAt oldVisit sourceIndex)
                ((contributionCapacityReopeningTemporalVisitAt oldVisit
                  sourceIndex (index + 1)).next next_eq) entry)
              entry_eq)
            advanced

/-- Runtime enters after the reopening root's first write. -/
def contributionCapacityReopenedVisitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  contributionCapacityReopeningTemporalVisitAt oldVisit sourceIndex (index + 1)

abbrev contributionCapacityReopenedAuthorityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  contributionCapacityReopeningResidualAuthorityAt oldVisit sourceIndex
    (index + 1)

def contributionCapacityReopenedInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ULift.up.{1, 0}
    ((CanonicalReopeningRootAt oldVisit sourceIndex).emitted
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index).current)

def contributionCapacityReopenedAnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeRootSemanticFaceAt
      (CanonicalReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index) where
  projection := ContributionCapacityReopeningProjection.answer
  active := PUnit.unit
  classifier_eq := rfl

theorem contributionCapacityReopenedAnswer_generates_residualCarryAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty (SourceGeneratedReopeningResidualCarryAt oldVisit
      sourceIndex (CanonicalReopeningSourceEventAt oldVisit sourceIndex)
      index) := by
  have generated :=
    (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index)
      |>.rootRead
  have current_eq :
      (show Nat from
        (contributionCapacityReopeningRootVisitAt oldVisit sourceIndex
          index).current) = index :=
    contributionCapacityReopeningVisit_current_exact oldVisit sourceIndex index
  simpa only [current_eq] using generated.down

def contributionCapacityReopenedAnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex index)
      (contributionCapacityReopeningTargetResidual oldVisit)
      (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index) where
  projection := ContributionCapacityReopeningProjection.consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacityReopenedCompilationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeInquiryCompilationAt
      (CanonicalReopeningRootAt oldVisit sourceIndex)
      (contributionCapacityReopenedVisitAt oldVisit sourceIndex index)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex index)
      (contributionCapacityReopeningTargetResidual oldVisit)
      (contributionCapacityReopenedAuthorityAt oldVisit sourceIndex index) :=
  .answered
    (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index)
    (contributionCapacityReopenedAnswerConsumerAt oldVisit sourceIndex index)

def contributionCapacityReopenedStateAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    RootInquiryStateAt (ReopeningNAt oldVisit)
      (ReopeningVAt oldVisit sourceIndex) where
  root := CanonicalReopeningRootAt oldVisit sourceIndex
  visit := contributionCapacityReopenedVisitAt oldVisit sourceIndex index
  U7 := contributionCapacityReopeningU7 oldVisit
  calculus := contributionCapacityReopeningCalculus oldVisit
  Query := Unit
  entryAt := fun _ => contributionCapacityReopeningTargetResidual oldVisit
  authorityAt := fun _ =>
    contributionCapacityReopenedAuthorityAt oldVisit sourceIndex index
  compilationProgramAt := fun _ =>
    { compile := fun _ => contributionCapacityReopenedCompilationAt oldVisit
        sourceIndex index }
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityReopeningProjection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audit_eq
    cases audit_eq

def contributionCapacityReopenedEngineStateAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  RootInquiryEngineStateAt.create
    (contributionCapacityReopenedStateAt oldVisit sourceIndex index)

def contributionCapacityReopenedPresentationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    RootInquiryStatePresentation where
  N := ReopeningNAt oldVisit
  V := ReopeningVAt oldVisit sourceIndex
  state := contributionCapacityReopenedEngineStateAt oldVisit sourceIndex index

@[simp] theorem contributionCapacityReopenedState_compiles_answered
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityReopenedStateAt oldVisit sourceIndex index).compileInquiry () =
      .answered
        (contributionCapacityReopenedAnswerFaceAt oldVisit sourceIndex index)
        (contributionCapacityReopenedAnswerConsumerAt oldVisit sourceIndex
          index) :=
  rfl

end
end M14SourceGeneratedContributionCapacityReopeningState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningState.contributionCapacityReopeningActionState_compiles_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningState.contributionCapacityReopenedState_compiles_answered
