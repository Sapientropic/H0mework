import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedFixtureLaw

/-!
# Whole universal six-class lifecycle regression

The neutral fixture regains all six lifecycle classes only through the
sealed universal law.  It also checks exact framework succession, domain
birth/exit, many-to-many overlap, unique next compilation, and rejection of
a raw nonidentity singleton method without a sealed framework edge.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace Lifecycle
namespace Universal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedAdapter

theorem fixed_survival :
    law.SurviveAt (sourceActor .s0) (targetActor .t0) := by
  have branch := law.singletonCompiler
    (sourceActor .s0) (targetActor .t0)
    singleton_s0_t0.1 singleton_s0_t0.2
  rw [law_installation] at branch
  cases branch with
  | inl identity => exact ⟨singleton_s0_t0.1, singleton_s0_t0.2, ⟨identity⟩⟩
  | inr succession => exact (succession.notIdentity identityAuthority).elim

private theorem identity_s5_t4_impossible :
    core.DomainIdentityTransportAt (sourceActor .s5) (targetActor .t4) →
      False := by
  intro identity
  have sourceEq := congrArg Subtype.val identity.source_eq
  cases sourceEq

theorem fixed_succession :
    law.SuccessionAt (sourceActor .s5) (targetActor .t4) := by
  have branch := law.singletonCompiler
    (sourceActor .s5) (targetActor .t4)
    singleton_s5_t4.1 singleton_s5_t4.2
  rw [law_installation] at branch
  cases branch with
  | inl identity => exact (identity_s5_t4_impossible identity).elim
  | inr succession =>
      change core.SingletonDescendantAt (sourceActor .s5) (targetActor .t4) ∧
        core.SingletonPredecessorAt (sourceActor .s5) (targetActor .t4) ∧
        Nonempty (InstalledSuccessionAt law.method.installation
          (sourceActor .s5) (targetActor .t4))
      rw [law_installation]
      exact ⟨singleton_s5_t4.1, singleton_s5_t4.2, ⟨succession⟩⟩

private theorem no_domain_reappearance
    {historical : core.HistoricalActorBefore} {target : core.TargetActor} :
    core.DomainReappearanceAt historical target → False := by
  intro reappearance
  exact nomatch reappearance.reappearance.1

theorem fixed_birth : law.BirthAt (targetActor .t5) := by
  have branch := law.emptyTargetCompiler (targetActor .t5) empty_t5
  rw [law_installation] at branch
  cases branch with
  | inl fresh =>
      change core.EmptyPredecessorAt (targetActor .t5) ∧
        Nonempty (FreshOriginAuthority law.method.installation
          (targetActor .t5))
      rw [law_installation]
      exact ⟨empty_t5, ⟨fresh⟩⟩
  | inr reappearance =>
      cases reappearance with
      | inl domain => exact (no_domain_reappearance domain.origin).elim
      | inr framework => exact nomatch framework.reopen.event

theorem fixed_exit : law.ExitAt (sourceActor .s4) := by
  have authority := law.emptySourceCompiler (sourceActor .s4) exit_s4
  exact ⟨exit_s4, ⟨authority⟩⟩

theorem fixed_split : core.SplitAt (sourceActor .s1) :=
  split_s1

theorem fixed_merge : core.MergeAt (targetActor .t3) :=
  merge_t3

theorem fixed_many_to_many :
    core.ActorRelated (sourceActor .s1) (targetActor .t1) ∧
      core.SplitAt (sourceActor .s1) ∧ core.MergeAt (targetActor .t1) :=
  ⟨relation_s1_t1, split_s1, merge_t1⟩

theorem fixed_source_census (source : core.SourceActor) :
    law.SourceSideClassified source :=
  law.source_side_exhaustive source

theorem fixed_target_census (target : core.TargetActor) :
    law.TargetSideClassified target :=
  law.target_side_exhaustive target

theorem fixed_link_census {source : core.SourceActor}
    {target : core.TargetActor} (link : core.ActorRelated source target) :
    core.SplitAt source ∨ core.MergeAt target ∨
      law.SurviveAt source target ∨ law.SuccessionAt source target :=
  law.related_links_exhaustive link

theorem fixed_succession_consumes_same_debt :
    ∃ authority : InstalledSuccessionAt law.method.installation
        (sourceActor .s5) (targetActor .t4),
      InstalledSuccessionHasExactProvenance law.method.installation
        authority :=
  fixed_succession.frameworkAuthority law

theorem fixed_birth_has_exact_origin :
    ∃ authority : FreshOriginAuthority law.method.installation
        (targetActor .t5),
      FreshOriginHasExactProvenance law.method.installation authority :=
  fixed_birth.exactOrigin law

theorem fixed_exit_has_exact_disposition :
    ∃ authority : ExitAuthority law.method.installation (sourceActor .s4),
      ExitHasExactProvenance law.method.installation authority :=
  fixed_exit.exactDisposition law

theorem fixed_next_is_adjacent_target :
    law.wholeCompilation.next? = some EventState.after :=
  law.wholeCompilation_next_eq_target

theorem fixed_compilation_unique
    (candidate : SourceOwnedActorLifecycleLaw.ActualLifecycleCompilation law) :
    candidate = law.wholeCompilation :=
  law.compilation_unique candidate

def absentMethod : SourceOwnedLifecycleAuthorityMethod.{0, 0, 0, 0} core where
  installation := .absent

theorem absentMethod_missing_nonidentity_singleton :
    ¬ SourceOwnedActorLifecycleLaw.SingletonCoverage absentMethod := by
  intro coverage
  rcases coverage (sourceActor .s5) (targetActor .t4)
      singleton_s5_t4.1 singleton_s5_t4.2 with ⟨branch⟩
  cases branch with
  | inl identity => exact identity_s5_t4_impossible identity
  | inr succession => exact nomatch succession.down

theorem absentMethod_is_rejected :
    SourceOwnedActorLifecycleLaw.compile? absentMethod = none :=
  SourceOwnedActorLifecycleLaw.compile?_eq_none_of_missing_singleton
    absentMethod absentMethod_missing_nonidentity_singleton

structure M1UniversalWholeProgramSink : Prop where
  sourceActorsExact : ∀ actor : core.SourceActor,
    ∃ seed : SourceSeed actualEventOccurrenceOf core.sourceFace.Seed
        core.sourceFace.SeedAt actualEventGame.source,
      (∃ state ∈ actualEventGame.occurrence.trace,
        state = core.sourceFace.state actualEventGame.source ∧
          core.sourceFace.SeedAt actualEventGame.source state seed.1) ∧
      core.sourceActorOf seed = actor
  targetActorsExact : ∀ actor : core.TargetActor,
    ∃ seed : SourceSeed actualEventOccurrenceOf core.targetFace.Seed
        core.targetFace.SeedAt actualEventGame.source,
      (∃ state ∈ actualEventGame.occurrence.trace,
        state = core.targetFace.state actualEventGame.source ∧
          core.targetFace.SeedAt actualEventGame.source state seed.1) ∧
      core.targetActorOf seed = actor
  birth : law.BirthAt (targetActor .t5)
  survive : law.SurviveAt (sourceActor .s0) (targetActor .t0)
  merge : core.MergeAt (targetActor .t3)
  split : core.SplitAt (sourceActor .s1)
  exit : law.ExitAt (sourceActor .s4)
  succession : law.SuccessionAt (sourceActor .s5) (targetActor .t4)
  sourceCensus : ∀ source, law.SourceSideClassified source
  targetCensus : ∀ target, law.TargetSideClassified target
  linkCensus : ∀ source target, core.ActorRelated source target →
    core.SplitAt source ∨ core.MergeAt target ∨
      law.SurviveAt source target ∨ law.SuccessionAt source target
  manyToMany : core.ActorRelated (sourceActor .s1) (targetActor .t1) ∧
    core.SplitAt (sourceActor .s1) ∧ core.MergeAt (targetActor .t1)
  successionProvenance :
    ∃ authority : InstalledSuccessionAt law.method.installation
        (sourceActor .s5) (targetActor .t4),
      InstalledSuccessionHasExactProvenance law.method.installation authority
  birthProvenance :
    ∃ authority : FreshOriginAuthority law.method.installation
        (targetActor .t5),
      FreshOriginHasExactProvenance law.method.installation authority
  exitProvenance :
    ∃ authority : ExitAuthority law.method.installation (sourceActor .s4),
      ExitHasExactProvenance law.method.installation authority
  next : law.wholeCompilation.next? = some EventState.after
  nextUnique : ∀ candidate :
      SourceOwnedActorLifecycleLaw.ActualLifecycleCompilation law,
    candidate = law.wholeCompilation
  missingSuccessionRejected :
    SourceOwnedActorLifecycleLaw.compile? absentMethod = none

theorem m1UniversalWholeProgramSink : M1UniversalWholeProgramSink where
  sourceActorsExact := core.sourceActor_has_exact_state_seed
  targetActorsExact := core.targetActor_has_exact_state_seed
  birth := fixed_birth
  survive := fixed_survival
  merge := fixed_merge
  split := fixed_split
  exit := fixed_exit
  succession := fixed_succession
  sourceCensus := fixed_source_census
  targetCensus := fixed_target_census
  linkCensus := fun _source _target link => fixed_link_census link
  manyToMany := fixed_many_to_many
  successionProvenance := fixed_succession_consumes_same_debt
  birthProvenance := fixed_birth_has_exact_origin
  exitProvenance := fixed_exit_has_exact_disposition
  next := fixed_next_is_adjacent_target
  nextUnique := fixed_compilation_unique
  missingSuccessionRejected := absentMethod_is_rejected

end Universal
end Lifecycle
end Society
end Regression
end ProcessGame
end SaturationMonoid
