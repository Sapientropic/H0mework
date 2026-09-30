import H0mework.Foundation.Agency.FibreExhaustion
import H0mework.Foundation.Agency.Installation

/-!
# Sealed universal actor lifecycle law

Private coverage validation, public six-class exhaustion and the unique
same-root whole lifecycle compilation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle
namespace Universal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w x

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game}

/-! ## The sole public source-owned law -/

/-- Raw sealed authority families.  This method contains no completeness
proof and is not itself a six-class producer. -/
structure SourceOwnedLifecycleAuthorityMethod
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game) where
  installation : FrameworkInstallation.{u, v, w, x} core

/-- Universal lifecycle producer.  Its constructor is private; the sole
producer is `compile?`, which validates all three coverage propositions from
the installed exact authority families. -/
structure SourceOwnedActorLifecycleLaw
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game) where
  private mk ::
  method : SourceOwnedLifecycleAuthorityMethod.{u, v, w, x} core
  singletonCoverage : ∀ source target,
    core.SingletonDescendantAt source target →
    core.SingletonPredecessorAt source target →
      core.DomainIdentityTransportAt source target ⊕
        InstalledSuccessionAt method.installation source target
  emptyTargetCoverage : ∀ target,
    core.EmptyPredecessorAt target →
      FreshOriginAuthority method.installation target ⊕
        ReappearanceAuthority method.installation target
  emptySourceCoverage : ∀ source,
    core.ExitAt source → ExitAuthority method.installation source

namespace SourceOwnedActorLifecycleLaw

def singletonCompiler (law : SourceOwnedActorLifecycleLaw core) :=
  law.singletonCoverage

def emptyTargetCompiler (law : SourceOwnedActorLifecycleLaw core) :=
  law.emptyTargetCoverage

def emptySourceCompiler (law : SourceOwnedActorLifecycleLaw core) :=
  law.emptySourceCoverage

def SingletonCoverage
    (method : SourceOwnedLifecycleAuthorityMethod core) : Prop :=
  ∀ source target,
    core.SingletonDescendantAt source target →
    core.SingletonPredecessorAt source target →
      Nonempty (core.DomainIdentityTransportAt source target ⊕
        InstalledSuccessionAt method.installation source target)

def EmptyTargetCoverage
    (method : SourceOwnedLifecycleAuthorityMethod core) : Prop :=
  ∀ target, core.EmptyPredecessorAt target →
    Nonempty (FreshOriginAuthority method.installation target ⊕
      ReappearanceAuthority method.installation target)

def EmptySourceCoverage
    (method : SourceOwnedLifecycleAuthorityMethod core) : Prop :=
  ∀ source, core.ExitAt source →
    Nonempty (ExitAuthority method.installation source)

/-- Sole law producer.  Completeness is inferred by classical validation of
the exact installed families; it is not submitted to a public constructor. -/
noncomputable def compile?
    (method : SourceOwnedLifecycleAuthorityMethod core) :
    Option (SourceOwnedActorLifecycleLaw core) := by
  classical
  by_cases singletonCoverage : SingletonCoverage method
  · by_cases emptyTargetCoverage : EmptyTargetCoverage method
    · by_cases emptySourceCoverage : EmptySourceCoverage method
      · exact some ⟨method,
          fun source target descendants predecessors =>
            Classical.choice
              (singletonCoverage source target descendants predecessors),
          fun target empty =>
            Classical.choice (emptyTargetCoverage target empty),
          fun source empty =>
            Classical.choice (emptySourceCoverage source empty)⟩
      · exact none
    · exact none
  · exact none

theorem compile?_isSome_iff
    (method : SourceOwnedLifecycleAuthorityMethod core) :
    (compile? method).isSome ↔
      SingletonCoverage method ∧ EmptyTargetCoverage method ∧
        EmptySourceCoverage method := by
  classical
  by_cases singleton : SingletonCoverage method
  · by_cases targets : EmptyTargetCoverage method
    · by_cases sources : EmptySourceCoverage method <;>
        simp [compile?, singleton, targets, sources]
    · simp [compile?, singleton, targets]
  · simp [compile?, singleton]

theorem compile?_eq_none_of_missing_singleton
    (method : SourceOwnedLifecycleAuthorityMethod core)
    (missing : ¬ SingletonCoverage method) :
    compile? method = none := by
  classical
  unfold compile?
  simp [missing]

theorem compile?_get_method
    (method : SourceOwnedLifecycleAuthorityMethod core)
    (present : (compile? method).isSome) :
    ((compile? method).get present).method = method := by
  classical
  have coverage := (compile?_isSome_iff method).mp present
  rcases coverage with ⟨singletons, targets, sources⟩
  simp [compile?, singletons, targets, sources]

private def classificationMethod
    (law : SourceOwnedActorLifecycleLaw core) :
    SourceOwnedLifecycleCore.ClassificationMethod core where
  IdentityTransportAt := core.DomainIdentityTransportAt
  SuccessionAuthorityAt :=
    InstalledSuccessionAt law.method.installation
  ExitAuthorityAt := ExitAuthority law.method.installation
  FreshOriginAt := FreshOriginAuthority law.method.installation
  ReappearanceAuthorityAt := ReappearanceAuthority law.method.installation
  singletonAuthority := law.singletonCompiler
  emptyTargetAuthority := law.emptyTargetCompiler
  emptySourceAuthority := law.emptySourceCompiler

/-! ## Stable six-class public mouth -/

def BirthAt (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.BirthAt target

def ReappearanceAt (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.ReappearanceAt target

def ExitAt (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) : Prop :=
  law.classificationMethod.ClassifiedExitAt source

def SurviveAt (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  law.classificationMethod.SurviveAt source target

def SuccessionAt (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) (target : core.TargetActor) : Prop :=
  law.classificationMethod.SuccessionAt source target

def MergeParticipantAt (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) : Prop :=
  law.classificationMethod.MergeParticipantAt source

def SplitDescendantAt (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.SplitDescendantAt target

def SurvivesFrom (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) : Prop :=
  law.classificationMethod.SurvivesFrom source

def SurvivesInto (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.SurvivesInto target

def SucceedsFrom (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) : Prop :=
  law.classificationMethod.SucceedsFrom source

def SucceedsInto (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.SucceedsInto target

/-- Reappearance and linked succession are the same public sixth class. -/
def TargetSuccessionAt (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.TargetSuccessionAt target

def SourceSideClassified (law : SourceOwnedActorLifecycleLaw core)
    (source : core.SourceActor) : Prop :=
  law.classificationMethod.SourceSideClassified source

def TargetSideClassified (law : SourceOwnedActorLifecycleLaw core)
    (target : core.TargetActor) : Prop :=
  law.classificationMethod.TargetSideClassified target

theorem related_links_exhaustive
    (law : SourceOwnedActorLifecycleLaw core)
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target) :
    core.SplitAt source ∨ core.MergeAt target ∨
      law.SurviveAt source target ∨ law.SuccessionAt source target := by
  exact law.classificationMethod.related_links_exhaustive link

theorem source_side_exhaustive
    (law : SourceOwnedActorLifecycleLaw core) (source : core.SourceActor) :
    law.SourceSideClassified source := by
  exact law.classificationMethod.source_side_exhaustive source

theorem target_side_exhaustive
    (law : SourceOwnedActorLifecycleLaw core) (target : core.TargetActor) :
    law.TargetSideClassified target := by
  exact law.classificationMethod.target_side_exhaustive target

theorem manyToMany_nonexclusive
    (law : SourceOwnedActorLifecycleLaw core)
    {source : core.SourceActor} {target : core.TargetActor}
    (link : core.ActorRelated source target)
    (split : core.SplitAt source) (merge : core.MergeAt target) :
    core.ActorRelated source target ∧ core.SplitAt source ∧
      core.MergeAt target ∧
      (core.SplitAt source ∨ core.MergeAt target ∨
        law.SurviveAt source target ∨ law.SuccessionAt source target) := by
  exact law.classificationMethod.manyToMany_nonexclusive link split merge

/-! ## Stable provenance consumers -/

theorem SuccessionAt.frameworkAuthority
    (law : SourceOwnedActorLifecycleLaw core)
    {source : core.SourceActor} {target : core.TargetActor}
    (succession : law.SuccessionAt source target) :
    ∃ authority : InstalledSuccessionAt law.method.installation source target,
      InstalledSuccessionHasExactProvenance law.method.installation
        authority := by
  rcases succession.2.2 with ⟨authority⟩
  exact ⟨authority,
    installedSuccession_hasExactProvenance law.method.installation authority⟩

theorem BirthAt.exactOrigin
    (law : SourceOwnedActorLifecycleLaw core)
    {target : core.TargetActor} (birth : law.BirthAt target) :
    ∃ authority : FreshOriginAuthority law.method.installation target,
      FreshOriginHasExactProvenance law.method.installation authority := by
  rcases birth.2 with ⟨authority⟩
  exact ⟨authority,
    freshOrigin_hasExactProvenance law.method.installation authority⟩

theorem TargetSuccessionAt.exactProvenance
    (law : SourceOwnedActorLifecycleLaw core)
    {target : core.TargetActor} (succession : law.TargetSuccessionAt target) :
    (∃ source : core.SourceActor,
      ∃ authority : InstalledSuccessionAt law.method.installation source target,
        InstalledSuccessionHasExactProvenance law.method.installation
          authority) ∨
      ∃ authority : ReappearanceAuthority law.method.installation target,
        ReappearanceHasExactProvenance law.method.installation authority := by
  rcases succession with reappearance | linked
  · rcases reappearance.2 with ⟨authority⟩
    exact Or.inr ⟨authority,
      reappearance_hasExactProvenance law.method.installation authority⟩
  · rcases linked with ⟨source, linked⟩
    rcases SuccessionAt.frameworkAuthority law linked with
      ⟨authority, provenance⟩
    exact Or.inl ⟨source, authority, provenance⟩

theorem ExitAt.exactDisposition
    (law : SourceOwnedActorLifecycleLaw core)
    {source : core.SourceActor} (exit : law.ExitAt source) :
    ∃ authority : ExitAuthority law.method.installation source,
      ExitHasExactProvenance law.method.installation authority := by
  rcases exit.2 with ⟨authority⟩
  exact ⟨authority,
    exit_hasExactProvenance law.method.installation authority⟩

/-! ## Same-root public compiler -/

structure ClosedLifecycleClassification
    (law : SourceOwnedActorLifecycleLaw core) : Prop where
  sourceCensus : ∀ source, law.SourceSideClassified source
  targetCensus : ∀ target, law.TargetSideClassified target
  linkCensus : ∀ source target, core.ActorRelated source target →
    core.SplitAt source ∨ core.MergeAt target ∨
      law.SurviveAt source target ∨ law.SuccessionAt source target

theorem closedLifecycleClassification
    (law : SourceOwnedActorLifecycleLaw core) :
    ClosedLifecycleClassification law where
  sourceCensus := law.source_side_exhaustive
  targetCensus := law.target_side_exhaustive
  linkCensus := fun _source _target link => law.related_links_exhaustive link

structure ActualLifecycleCompilation
    (law : SourceOwnedActorLifecycleLaw core) where
  classification : ClosedLifecycleClassification law
  next? : Option State
  next_commutes : next? =
    game.occurrence.trace[core.sourceIndex + 1]?

def wholeCompilation (law : SourceOwnedActorLifecycleLaw core) :
    ActualLifecycleCompilation law where
  classification := law.closedLifecycleClassification
  next? := game.occurrence.trace[core.sourceIndex + 1]?
  next_commutes := rfl

theorem wholeCompilation_next_eq_target
    (law : SourceOwnedActorLifecycleLaw core) :
    law.wholeCompilation.next? = some (core.targetFace.state game.source) :=
  core.target_follows_source

theorem compilation_unique (law : SourceOwnedActorLifecycleLaw core)
    (candidate : ActualLifecycleCompilation law) :
    candidate = law.wholeCompilation := by
  cases candidate with
  | mk classification next nextCommutes =>
      have classificationEq :
          classification = law.wholeCompilation.classification :=
        Subsingleton.elim _ _
      have nextEq : next = law.wholeCompilation.next? := by
        change next = game.occurrence.trace[
          core.sourceIndex + 1]?
        exact nextCommutes
      cases classificationEq
      cases nextEq
      rfl

end SourceOwnedActorLifecycleLaw
end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
