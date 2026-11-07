import H0mework.Foundation.Agency.LifecycleLaw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.Lifecycle.Universal.FrameworkBoundaryAuthorityRegression
/-!
# Exact reappearance is target-side succession

The source boundary face is empty, while one historical actor reappears as
the unique target actor.  The framework half reuses the existing exact
terminal-to-reopen edge; no new vocabulary or responsibility process is
installed here.
-/
set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace Lifecycle
namespace Universal
namespace ReappearanceSuccessionRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal
open FrameworkBoundaryAuthorityRegression

def emptySourceFace : M0BoundaryFace actualEventOccurrenceOf where
  Seed := Empty
  Lineage := fun _ => Unit
  SeedAt := fun _ state _ => state = .before
  lineageOf := by
    intro source seed
    exact nomatch seed.1
  state := fun _ => .before
  seedAt_state := by
    intro source current seed active
    exact active

def singletonTargetFace : M0BoundaryFace actualEventOccurrenceOf where
  Seed := Unit
  Lineage := fun _ => Unit
  SeedAt := fun _ state _ => state = .after
  lineageOf := fun _ _ => ()
  state := fun _ => .after
  seedAt_state := by
    intro source current seed active
    exact active

def historySeedAt (_source : Unit) (state : EventState) (_seed : Unit) : Prop :=
  state = .before

def core : SourceOwnedLifecycleCore actualEventOccurrenceOf actualEventGame where
  sourceFace := emptySourceFace
  targetFace := singletonTargetFace
  HistorySeed := Unit
  HistoryLineage := fun _ => Unit
  historySeedAt := historySeedAt
  historyLineageOf := fun _ _ => ()
  LinkSeed := Empty
  linkAdmittedAt := fun link => nomatch link
  linkSource := fun link => nomatch link
  linkTarget := fun link => nomatch link
  linkSource_active := by intro link; exact nomatch link
  linkTarget_active := by intro link; exact nomatch link
  IdentitySeed := Empty
  identityAdmittedAt := fun identity => nomatch identity
  identitySource := fun identity => nomatch identity
  identityTarget := fun identity => nomatch identity
  identitySource_active := by intro identity; exact nomatch identity
  identityTarget_active := by intro identity; exact nomatch identity
  ExitSeed := Empty
  exitAdmittedAt := fun exit => nomatch exit
  exitSource := fun exit => nomatch exit
  exitSource_active := by intro exit; exact nomatch exit
  FreshSeed := Empty
  freshAdmittedAt := fun fresh => nomatch fresh
  freshTarget := fun fresh => nomatch fresh
  freshTarget_active := by intro fresh; exact nomatch fresh
  ReappearanceSeed := Unit
  reappearanceAdmittedAt := fun _ => True
  reappearanceHistory := fun _ => ()
  reappearanceHistoryState := fun _ => .before
  reappearanceHistory_active := by intro reappearance admitted; rfl
  reappearanceTarget := fun _ => ()
  reappearanceTarget_active := by intro reappearance admitted; rfl
  sourceIndex := 0
  source_state_mem := by simp [actualEventOccurrenceOf, emptySourceFace]
  target_state_mem := by simp [actualEventOccurrenceOf, singletonTargetFace]
  source_at_index := rfl
  target_follows_source := rfl
  history_before_event := by
    intro state seed active
    subst state
    simp [actualEventOccurrenceOf]

private theorem noSourceActor (source : core.SourceActor) : False := by
  rcases source.2 with ⟨seed, generated⟩
  exact nomatch seed.1

def targetSeed : SourceSeed actualEventOccurrenceOf core.targetFace.Seed
    core.targetFace.SeedAt actualEventGame.source :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl⟩

def targetActor : core.TargetActor :=
  core.targetActorOf targetSeed

def historicalSeed : SourceSeed actualEventOccurrenceOf core.HistorySeed
    core.historySeedAt actualEventGame.source :=
  ⟨(), .before, by simp [actualEventOccurrenceOf], rfl⟩

def historicalActor : core.HistoricalActorBefore :=
  generatedActorOf actualEventGame core.HistorySeed core.historySeedAt
    core.HistoryLineage core.historyLineageOf historicalSeed

private theorem target_eq (target : core.TargetActor) : target = targetActor := by
  apply Subtype.ext
  cases target.1
  rfl

def exactReappearance : core.ExactReappearanceSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def domainReappearance :
    core.DomainReappearanceAt historicalActor targetActor where
  reappearance := exactReappearance
  historical_eq := rfl
  target_eq := rfl

theorem emptyPredecessor (target : core.TargetActor) :
    core.EmptyPredecessorAt target := by
  intro source related
  exact noSourceActor source

abbrev ReopenV := V
abbrev ReopenP := P

def incidenceCompiler : ActorResponsibilityIncidenceCompiler core ReopenV where
  SourceSeed := Empty
  sourceAdmittedAt := fun seed => nomatch seed
  sourceActorSeed := fun seed => nomatch seed
  sourceActor_active := by intro seed; exact nomatch seed
  sourceObligation := fun seed => nomatch seed
  sourceEvent := fun seed => nomatch seed
  TargetSeed := Unit
  targetAdmittedAt := fun _ => True
  targetActorSeed := fun _ => ()
  targetActor_active := by intro seed admitted; rfl
  targetObligation := fun _ => reopenAuthority.targetObligation ReopenP
  targetEvent := fun _ => (ReopenP.reopenPayload reopenAuthority.event).sourceEvent
  HistoricalSeed := Unit
  historicalAdmittedAt := fun _ => True
  historicalActorSeed := fun _ => ()
  historicalActorState := fun _ => .before
  historicalActor_active := by intro seed admitted; rfl
  historicalObligation := fun _ => reopenAuthority.archive.obligation
  historicalEvent := fun _ =>
    (ReopenP.reopenPayload reopenAuthority.event).sourceEvent

def targetIncidenceSeed : incidenceCompiler.ExactTargetSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def historicalIncidenceSeed : incidenceCompiler.ExactHistoricalSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def targetResponsibility : incidenceCompiler.TargetResponsibilityAt targetActor
    (reopenAuthority.targetObligation ReopenP)
    (ReopenP.reopenPayload reopenAuthority.event).sourceEvent where
  seed := targetIncidenceSeed
  actor_eq := rfl
  obligation_eq := rfl
  sourceEvent_eq := rfl

def historicalResponsibility : incidenceCompiler.HistoricalResponsibilityAt
    historicalActor reopenAuthority.archive.obligation
    (ReopenP.reopenPayload reopenAuthority.event).sourceEvent where
  seed := historicalIncidenceSeed
  actor_eq := rfl
  obligation_eq := rfl
  sourceEvent_eq := rfl

def incidence : ActorResponsibilityIncidence core ReopenV where
  compiler := incidenceCompiler
  source_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    exact nomatch firstAt.seed.1
  target_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    exact (target_eq first).trans (target_eq last).symm
  historical_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    apply Subtype.ext
    cases first.1
    cases last.1
    rfl

def exactFrameworkReappearance :
    ExactReappearanceAuthority core ReopenP incidence targetActor where
  historical := historicalActor
  historicalIdentity := domainReappearance
  sourceState := terminalState
  edge := reopenEdge
  reopen := reopenAuthority
  historicalResponsibility := by
    simpa [incidence] using historicalResponsibility
  targetResponsibility := by
    simpa [incidence] using targetResponsibility

def installation : FrameworkInstallation core :=
  .installed ReopenV ReopenP incidence

def reappearanceAuthority : ReappearanceAuthority installation targetActor :=
  .inr exactFrameworkReappearance

def method : SourceOwnedLifecycleAuthorityMethod core where
  installation := installation

theorem singletonCoverage :
    SourceOwnedActorLifecycleLaw.SingletonCoverage method := by
  intro source
  exact (noSourceActor source).elim

theorem emptyTargetCoverage :
    SourceOwnedActorLifecycleLaw.EmptyTargetCoverage method := by
  intro target empty
  have targetValue := target_eq target
  subst target
  exact ⟨.inr reappearanceAuthority⟩

theorem emptySourceCoverage :
    SourceOwnedActorLifecycleLaw.EmptySourceCoverage method := by
  intro source
  exact (noSourceActor source).elim

theorem compile?_isSome :
    (SourceOwnedActorLifecycleLaw.compile? method).isSome := by
  apply (SourceOwnedActorLifecycleLaw.compile?_isSome_iff method).2
  exact ⟨singletonCoverage, emptyTargetCoverage, emptySourceCoverage⟩

noncomputable def law : SourceOwnedActorLifecycleLaw core :=
  (SourceOwnedActorLifecycleLaw.compile? method).get compile?_isSome

@[simp] theorem law_installation : law.method.installation = installation := by
  have methodEq :=
    SourceOwnedActorLifecycleLaw.compile?_get_method method compile?_isSome
  exact congrArg SourceOwnedLifecycleAuthorityMethod.installation methodEq

theorem target_reappears : law.ReappearanceAt targetActor := by
  change core.EmptyPredecessorAt targetActor ∧
    Nonempty (ReappearanceAuthority law.method.installation targetActor)
  rw [law_installation]
  exact ⟨emptyPredecessor targetActor, ⟨reappearanceAuthority⟩⟩

theorem target_succession : law.TargetSuccessionAt targetActor :=
  Or.inl target_reappears

theorem target_not_birth : ¬ law.BirthAt targetActor := by
  intro birth
  change core.EmptyPredecessorAt targetActor ∧
    Nonempty (FreshOriginAuthority law.method.installation targetActor) at birth
  rcases birth.2 with ⟨authority⟩
  rw [law_installation] at authority
  cases authority with
  | inl domain => exact nomatch domain.origin.fresh.1
  | inr framework =>
      exact framework.noHistoricalIdentity historicalActor domainReappearance

theorem reappearance_same_debt :
    SameDebtLineage reopenAuthority.archive.obligation
      (reopenAuthority.targetObligation ReopenP) :=
  exactFrameworkReappearance.sameDebtLineage

def reappearance_anchorTransport :
    SourceAnchorTransport reopenAuthority.archive.obligation.sourceAnchor
      (reopenAuthority.targetObligation ReopenP).sourceAnchor :=
  exactFrameworkReappearance.reopen.anchorTransport ReopenP

theorem reappearance_next_slot :
    reopenEdge.target.slots[reopenAuthority.slot ReopenP]? =
      some (.live (reopenAuthority.targetObligation ReopenP)) :=
  exactFrameworkReappearance.reopen.target_slot ReopenP

theorem target_succession_consumes_reappearance :
    ∃ authority : ReappearanceAuthority law.method.installation targetActor,
      ReappearanceHasExactProvenance law.method.installation authority := by
  rcases target_succession.exactProvenance law with linked | reappeared
  · rcases linked with ⟨source, authority, provenance⟩
    exact (noSourceActor source).elim
  · exact reappeared

theorem whole_next : law.wholeCompilation.next? = some EventState.after :=
  law.wholeCompilation_next_eq_target

end ReappearanceSuccessionRegression
end Universal
end Lifecycle
end Society
end Regression
end ProcessGame
end SaturationMonoid
