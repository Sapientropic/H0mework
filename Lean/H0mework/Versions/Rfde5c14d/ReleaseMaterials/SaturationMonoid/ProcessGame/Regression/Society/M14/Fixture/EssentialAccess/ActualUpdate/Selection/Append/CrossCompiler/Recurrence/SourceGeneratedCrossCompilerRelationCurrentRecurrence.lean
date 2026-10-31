import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrenceStage
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Incidence.Source.SourceGeneratedEssentialAccessRelationRenewal

/-!
# Source-generated heterogeneous relation-current recurrence

The first cross-compiler bridge consumes the already installed relation
selection at stage one.  Every later stage grows the atom universe by one
right summand, left-embeds the complete prior occurrence, and generates its
new right root from the current fold.  The recursion stores no future table
and exposes no caller seed, current, branch or compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerRelationCurrentRecurrence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14EssentialAccessRelationFixture
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrenceStage.RelationLineageRecurrenceStage
open M14SourceGeneratedEssentialAccessRelationRenewal

abbrev ExactRelationSeed :=
  essentialAccessRelationCompiler.ExactRelationSeed

/-- Each actual cross write adds exactly one newly generated seed summand. -/
def CrossCompilerAtomAt : Nat → Type
  | 0 => ExactRelationSeed
  | depth + 1 => CrossCompilerAtomAt depth ⊕ ExactRelationSeed

def crossCompilerAtomSeedAt : (depth : Nat) →
    CrossCompilerAtomAt depth → ExactRelationSeed
  | 0 => id
  | depth + 1 => Sum.elim (crossCompilerAtomSeedAt depth) id

def crossCompilerSeedFoldAlgebraAt (depth : Nat)
    (origin : CrossCompilerAtomAt depth)
    (_children : List ExactRelationSeed) : ExactRelationSeed :=
  sourceGeneratedEssentialAccessRenewalSeed
    (crossCompilerAtomSeedAt depth origin)

def crossCompilerCurrentSeedAt (depth : Nat)
    (current : RootedAccountedUnfolding (CrossCompilerAtomAt depth)) :
    ExactRelationSeed :=
  current.fold (crossCompilerSeedFoldAlgebraAt depth)

def retainedCrossCompilerCurrentAt {depth : Nat}
    (current : RootedAccountedUnfolding (CrossCompilerAtomAt depth)) :
    RootedAccountedUnfolding (CrossCompilerAtomAt depth) :=
  .occur current.root (AccountedBranches.singleton current)

/-- One private heterogeneous stage.  Only its action current is stored; the
seed and target current are certified as folds and coproduct writes. -/
structure SourceGeneratedCrossCompilerRelationCurrentStageAt
    (depth : Nat) : Type where
  private mk ::
  actionCurrent : RootedAccountedUnfolding (CrossCompilerAtomAt depth)
  targetSeed : ExactRelationSeed
  targetSeedExact : targetSeed =
    crossCompilerCurrentSeedAt depth actionCurrent
  targetCurrent :
    RootedAccountedUnfolding (CrossCompilerAtomAt (depth + 1))
  targetCurrentExact : targetCurrent =
    .occur (.inr targetSeed)
      (AccountedBranches.singleton (actionCurrent.map Sum.inl))

namespace SourceGeneratedCrossCompilerRelationCurrentStageAt

private def first :
    SourceGeneratedCrossCompilerRelationCurrentStageAt 0 :=
  let actionCurrent := (stageAt 1).actionCurrent
  let targetSeed := crossCompilerCurrentSeedAt 0 actionCurrent
  { actionCurrent := actionCurrent
    targetSeed := targetSeed
    targetSeedExact := rfl
    targetCurrent :=
      .occur (.inr targetSeed)
        (AccountedBranches.singleton (actionCurrent.map Sum.inl))
    targetCurrentExact := rfl }

private def next {depth : Nat}
    (stage : SourceGeneratedCrossCompilerRelationCurrentStageAt depth) :
    SourceGeneratedCrossCompilerRelationCurrentStageAt (depth + 1) :=
  let actionCurrent := retainedCrossCompilerCurrentAt stage.targetCurrent
  let targetSeed := crossCompilerCurrentSeedAt (depth + 1) actionCurrent
  { actionCurrent := actionCurrent
    targetSeed := targetSeed
    targetSeedExact := rfl
    targetCurrent :=
      .occur (.inr targetSeed)
        (AccountedBranches.singleton (actionCurrent.map Sum.inl))
    targetCurrentExact := rfl }

end SourceGeneratedCrossCompilerRelationCurrentStageAt

/-- Recursive producer.  `Nat` iterates the generated `next` operation; it
does not index a stored action, target or event table. -/
def crossCompilerCurrentStageAt :
    (depth : Nat) → SourceGeneratedCrossCompilerRelationCurrentStageAt depth
  | 0 => SourceGeneratedCrossCompilerRelationCurrentStageAt.first
  | depth + 1 =>
      SourceGeneratedCrossCompilerRelationCurrentStageAt.next
        (crossCompilerCurrentStageAt depth)

@[simp] theorem crossCompilerCurrentStageAt_zero_actionCurrent :
    (crossCompilerCurrentStageAt 0).actionCurrent =
      (stageAt 1).actionCurrent :=
  rfl

@[simp] theorem crossCompilerCurrentStageAt_succ_actionCurrent
    (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 1)).actionCurrent =
      retainedCrossCompilerCurrentAt
        (crossCompilerCurrentStageAt depth).targetCurrent :=
  rfl

@[simp] theorem crossCompilerCurrentStageAt_targetRoot_exact
    (depth : Nat) :
    (crossCompilerCurrentStageAt depth).targetCurrent.root =
      .inr (crossCompilerCurrentStageAt depth).targetSeed := by
  rw [(crossCompilerCurrentStageAt depth).targetCurrentExact]
  rfl

@[simp] theorem crossCompilerCurrentStageAt_targetBranches_exact
    (depth : Nat) :
    (crossCompilerCurrentStageAt depth).targetCurrent.branches =
      AccountedBranches.singleton
        ((crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl) := by
  rw [(crossCompilerCurrentStageAt depth).targetCurrentExact]
  rfl

theorem crossCompilerCurrentStageAt_seed_fold_unique
    (depth : Nat)
    (candidate :
      RootedAccountedUnfolding (CrossCompilerAtomAt depth) →
        ExactRelationSeed)
    (commutes : ∀ (origin : CrossCompilerAtomAt depth)
      (branches : AccountedBranches (CrossCompilerAtomAt depth)),
      candidate (.occur origin branches) =
        crossCompilerSeedFoldAlgebraAt depth origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    (crossCompilerCurrentStageAt depth).targetSeed =
      candidate (crossCompilerCurrentStageAt depth).actionCurrent := by
  rw [(crossCompilerCurrentStageAt depth).targetSeedExact]
  exact (RootedAccountedUnfolding.fold_unique
    (crossCompilerSeedFoldAlgebraAt depth) candidate commutes
      (crossCompilerCurrentStageAt depth).actionCurrent).symm

@[simp] theorem crossCompilerCurrentStageAt_targetSeed_succ
    (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 1)).targetSeed =
      sourceGeneratedEssentialAccessRenewalSeed
        (crossCompilerCurrentStageAt depth).targetSeed := by
  rw [(crossCompilerCurrentStageAt (depth + 1)).targetSeedExact]
  change sourceGeneratedEssentialAccessRenewalSeed
    (crossCompilerAtomSeedAt (depth + 1)
      (crossCompilerCurrentStageAt (depth + 1)).actionCurrent.root) = _
  rw [crossCompilerCurrentStageAt_succ_actionCurrent]
  change sourceGeneratedEssentialAccessRenewalSeed
    (crossCompilerAtomSeedAt (depth + 1)
      (crossCompilerCurrentStageAt depth).targetCurrent.root) = _
  rw [crossCompilerCurrentStageAt_targetRoot_exact]
  rfl

theorem crossCompilerCurrentStageAt_targetSeed_ne_succ (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 1)).targetSeed ≠
      (crossCompilerCurrentStageAt depth).targetSeed := by
  rw [crossCompilerCurrentStageAt_targetSeed_succ]
  exact renewalSeed_ne _

/-- Three actual cross writes renew the same relation-lineage identity at a
later occurrence. -/
theorem crossCompilerCurrentStageAt_targetSeed_add_three (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 3)).targetSeed =
      (crossCompilerCurrentStageAt depth).targetSeed := by
  calc
    (crossCompilerCurrentStageAt (depth + 3)).targetSeed =
        sourceGeneratedEssentialAccessRenewalSeed
          (crossCompilerCurrentStageAt (depth + 2)).targetSeed := by
            rw [show depth + 3 = (depth + 2) + 1 by omega,
              crossCompilerCurrentStageAt_targetSeed_succ]
    _ = sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed
            (crossCompilerCurrentStageAt (depth + 1)).targetSeed) := by
          rw [crossCompilerCurrentStageAt_targetSeed_succ (depth + 1)]
    _ = sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed
            (sourceGeneratedEssentialAccessRenewalSeed
              (crossCompilerCurrentStageAt depth).targetSeed)) := by
          rw [crossCompilerCurrentStageAt_targetSeed_succ depth]
    _ = (crossCompilerCurrentStageAt depth).targetSeed :=
      renewalSeed_three _

theorem crossCompilerCurrentStageAt_targetActor_add_three (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 3)).targetSeed.actor
        essentialAccessRelationCompiler =
      (crossCompilerCurrentStageAt depth).targetSeed.actor
        essentialAccessRelationCompiler := by
  rw [crossCompilerCurrentStageAt_targetSeed_add_three]

theorem crossCompilerCurrentStageAt_directConsumer (depth : Nat) :
    (crossCompilerCurrentStageAt depth).targetSeed =
        crossCompilerCurrentSeedAt depth
          (crossCompilerCurrentStageAt depth).actionCurrent ∧
      (crossCompilerCurrentStageAt depth).targetCurrent.root =
        .inr (crossCompilerCurrentStageAt depth).targetSeed ∧
      (crossCompilerCurrentStageAt depth).targetCurrent.branches =
        AccountedBranches.singleton
          ((crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl) :=
  ⟨(crossCompilerCurrentStageAt depth).targetSeedExact,
    crossCompilerCurrentStageAt_targetRoot_exact depth,
    crossCompilerCurrentStageAt_targetBranches_exact depth⟩

theorem crossCompilerCurrentStageAt_oldOnlyReconstruction_isEmpty
    (depth : Nat)
    (old : RootedAccountedUnfolding (CrossCompilerAtomAt depth)) :
    IsEmpty ((crossCompilerCurrentStageAt depth).targetCurrent =
      old.map Sum.inl) := by
  constructor
  intro equality
  have roots := congrArg RootedAccountedUnfolding.root equality
  rw [crossCompilerCurrentStageAt_targetRoot_exact] at roots
  change
    (Sum.inr (crossCompilerCurrentStageAt depth).targetSeed :
      CrossCompilerAtomAt depth ⊕ ExactRelationSeed) =
      (old.map Sum.inl).root at roots
  rw [RootedAccountedUnfolding.root_map] at roots
  cases roots

theorem crossCompilerCurrentStageAt_callerTargetSeedReplacement_isEmpty
    (depth : Nat) (replacement : ExactRelationSeed)
    (different : replacement ≠
      (crossCompilerCurrentStageAt depth).targetSeed) :
    IsEmpty ((crossCompilerCurrentStageAt depth).targetCurrent.root =
      .inr replacement) := by
  constructor
  intro equality
  rw [crossCompilerCurrentStageAt_targetRoot_exact] at equality
  exact different (Sum.inr.inj equality).symm

end
end M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_seed_fold_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_targetSeed_succ
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_targetSeed_ne_succ
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_targetSeed_add_three
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_targetActor_add_three
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_oldOnlyReconstruction_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt_callerTargetSeedReplacement_isEmpty
