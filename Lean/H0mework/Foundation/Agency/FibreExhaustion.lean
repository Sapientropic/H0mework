import H0mework.Foundation.Agency.Boundary

/-!
# Universal lifecycle fibre exhaustion

This module is the authority-neutral fibre algebra.  All completeness data is
owned by one dependent classification method; no theorem accepts a free
relation, target list, lifecycle label, or per-call completeness premise.
The final lifecycle compiler installs only framework-realized authority
families into this method.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle
namespace Universal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w z₁ z₂ z₃ z₄ z₅

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}

namespace SourceOwnedLifecycleCore

def EmptyPredecessorAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (target : core.TargetActor) : Prop :=
  ∀ source, ¬ core.ActorRelated source target

def ExitAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (source : core.SourceActor) : Prop :=
  ∀ target, ¬ core.ActorRelated source target

def SplitAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (source : core.SourceActor) : Prop :=
  ∃ left right,
    core.ActorRelated source left ∧ core.ActorRelated source right ∧
      left ≠ right

def MergeAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (target : core.TargetActor) : Prop :=
  ∃ left right,
    core.ActorRelated left target ∧ core.ActorRelated right target ∧
      left ≠ right

def SingletonDescendantAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  core.ActorRelated source target ∧
    ∀ candidate, core.ActorRelated source candidate → candidate = target

def SingletonPredecessorAt
    (core : SourceOwnedLifecycleCore occurrenceOf game)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  core.ActorRelated source target ∧
    ∀ candidate, core.ActorRelated candidate target → candidate = source

set_option linter.checkUnivs false in
/-- Source-owned lower authority families and their two total branch methods.
The final lifecycle layer seals these families to exact transport and
framework-edge receipts. -/
structure ClassificationMethod
    (core : SourceOwnedLifecycleCore occurrenceOf game) where
  IdentityTransportAt : core.SourceActor → core.TargetActor → Type z₁
  SuccessionAuthorityAt : core.SourceActor → core.TargetActor → Type z₂
  ExitAuthorityAt : core.SourceActor → Type z₃
  FreshOriginAt : core.TargetActor → Type z₄
  ReappearanceAuthorityAt : core.TargetActor → Type z₅
  singletonAuthority : ∀ source target,
    core.SingletonDescendantAt source target →
    core.SingletonPredecessorAt source target →
      IdentityTransportAt source target ⊕
        SuccessionAuthorityAt source target
  emptyTargetAuthority : ∀ target,
    core.EmptyPredecessorAt target →
      FreshOriginAt target ⊕ ReappearanceAuthorityAt target
  emptySourceAuthority : ∀ source,
    core.ExitAt source → ExitAuthorityAt source

namespace ClassificationMethod

def ClassifiedExitAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (source : core.SourceActor) : Prop :=
  core.ExitAt source ∧ Nonempty (method.ExitAuthorityAt source)

def BirthAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  core.EmptyPredecessorAt target ∧ Nonempty (method.FreshOriginAt target)

def ReappearanceAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  core.EmptyPredecessorAt target ∧
    Nonempty (method.ReappearanceAuthorityAt target)

def SurviveAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  core.SingletonDescendantAt source target ∧
    core.SingletonPredecessorAt source target ∧
    Nonempty (method.IdentityTransportAt source target)

def SuccessionAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  core.SingletonDescendantAt source target ∧
    core.SingletonPredecessorAt source target ∧
    Nonempty (method.SuccessionAuthorityAt source target)

def MergeParticipantAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (_method : ClassificationMethod core) (source : core.SourceActor) : Prop :=
  ∃ target, core.ActorRelated source target ∧ core.MergeAt target

def SplitDescendantAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (_method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  ∃ source, core.ActorRelated source target ∧ core.SplitAt source

def SurvivesFrom
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (source : core.SourceActor) : Prop :=
  ∃ target, method.SurviveAt source target

def SurvivesInto
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  ∃ source, method.SurviveAt source target

def SucceedsFrom
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (source : core.SourceActor) : Prop :=
  ∃ target, method.SuccessionAt source target

def SucceedsInto
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  ∃ source, method.SuccessionAt source target

/-- Public target-side succession includes both a linked bearer/supersession
event and an empty-predecessor reappearance backed by an exact reopen
authority. -/
def TargetSuccessionAt
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  method.ReappearanceAt target ∨ method.SucceedsInto target

theorem singletonDescendant_of_related_of_not_split
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target)
    (notSplit : ¬ core.SplitAt source) :
    core.SingletonDescendantAt source target := by
  refine ⟨link, ?_⟩
  intro candidate candidateLink
  apply Classical.byContradiction
  intro different
  exact notSplit ⟨target, candidate, link, candidateLink,
    fun equal => different equal.symm⟩

theorem singletonPredecessor_of_related_of_not_merge
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target)
    (notMerge : ¬ core.MergeAt target) :
    core.SingletonPredecessorAt source target := by
  refine ⟨link, ?_⟩
  intro candidate candidateLink
  apply Classical.byContradiction
  intro different
  exact notMerge ⟨source, candidate, link, candidateLink,
    fun equal => different equal.symm⟩

/-- Every exact event link is covered.  The disjunction is intentionally
nonexclusive: a many-to-many link may satisfy both split and merge. -/
theorem related_links_exhaustive
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core)
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target) :
    core.SplitAt source ∨ core.MergeAt target ∨
      method.SurviveAt source target ∨ method.SuccessionAt source target := by
  classical
  by_cases split : core.SplitAt source
  · exact Or.inl split
  by_cases merge : core.MergeAt target
  · exact Or.inr (Or.inl merge)
  have singletonDescendant :=
    singletonDescendant_of_related_of_not_split link split
  have singletonPredecessor :=
    singletonPredecessor_of_related_of_not_merge link merge
  rcases method.singletonAuthority source target singletonDescendant
      singletonPredecessor with identity | succession
  · exact Or.inr (Or.inr (Or.inl
      ⟨singletonDescendant, singletonPredecessor, ⟨identity⟩⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨singletonDescendant, singletonPredecessor, ⟨succession⟩⟩))

def SourceSideClassified
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (source : core.SourceActor) : Prop :=
  method.ClassifiedExitAt source ∨ core.SplitAt source ∨
    method.MergeParticipantAt source ∨ method.SurvivesFrom source ∨
      method.SucceedsFrom source

def TargetSideClassified
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) : Prop :=
  method.BirthAt target ∨ core.MergeAt target ∨
    method.SplitDescendantAt target ∨ method.SurvivesInto target ∨
      method.TargetSuccessionAt target

theorem source_side_exhaustive
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (source : core.SourceActor) :
    method.SourceSideClassified source := by
  classical
  by_cases hasDescendant : ∃ target, core.ActorRelated source target
  · rcases hasDescendant with ⟨target, link⟩
    rcases method.related_links_exhaustive link with
      split | merge | survives | succeeds
    · exact Or.inr (Or.inl split)
    · exact Or.inr (Or.inr (Or.inl ⟨target, link, merge⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨target, survives⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨target, succeeds⟩)))
  · have empty : core.ExitAt source :=
      fun target link => hasDescendant ⟨target, link⟩
    exact Or.inl ⟨empty, ⟨method.emptySourceAuthority source empty⟩⟩

theorem target_side_exhaustive
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core) (target : core.TargetActor) :
    method.TargetSideClassified target := by
  classical
  by_cases hasPredecessor : ∃ source, core.ActorRelated source target
  · rcases hasPredecessor with ⟨source, link⟩
    rcases method.related_links_exhaustive link with
      split | merge | survives | succeeds
    · exact Or.inr (Or.inr (Or.inl ⟨source, link, split⟩))
    · exact Or.inr (Or.inl merge)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨source, survives⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨source, succeeds⟩))))
  · have empty : core.EmptyPredecessorAt target :=
      fun source link => hasPredecessor ⟨source, link⟩
    rcases method.emptyTargetAuthority target empty with fresh | reappearance
    · exact Or.inl ⟨empty, ⟨fresh⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨empty, ⟨reappearance⟩⟩))))

theorem manyToMany_nonexclusive
    {core : SourceOwnedLifecycleCore occurrenceOf game}
    (method : ClassificationMethod core)
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target)
    (split : core.SplitAt source) (merge : core.MergeAt target) :
    core.ActorRelated source target ∧ core.SplitAt source ∧
      core.MergeAt target ∧
      (core.SplitAt source ∨ core.MergeAt target ∨
        method.SurviveAt source target ∨ method.SuccessionAt source target) :=
  ⟨link, split, merge, Or.inl split⟩

end ClassificationMethod
end SourceOwnedLifecycleCore
end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
