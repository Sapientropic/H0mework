import H0mework.Foundation.Agency.LifecycleLaw
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedFixtureCore
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.AcceptedResponsibilityTransfer

/-!
# Sealed universal law for the fixed six-class fixture

This adapter installs one real responsibility process edge for the sole
nonidentity singleton succession.  Birth and exit remain exact domain
authorities; no dummy responsibility process is used for them.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle
namespace Universal
namespace FixedAdapter

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Society.Lifecycle

abbrev V := LifecycleVocabulary

local instance : DecidableEq V.Bearer := instDecidableEqActorBearer

inductive BoundaryEvent : AdmittedObligation V → Type
  | succession : BoundaryEvent sourceObligation

def boundarySource {obligation : AdmittedObligation V} :
    BoundaryEvent obligation → V.SourceEvent
  | .succession => .after

def boundaryDisposition {obligation : AdmittedObligation V}
    (event : BoundaryEvent obligation) :
    BoundaryDisposition V obligation (boundarySource event) :=
  match event with
  | .succession => .carry acceptedTransferCarry

def process : NativeResponsibilityProcess V where
  AdmissionEvent := Empty
  admissionPayload := fun event => nomatch event
  BoundaryEvent := BoundaryEvent
  boundarySource := boundarySource
  boundary_anchor_eq := by
    intro obligation event
    cases event
    rfl
  boundary_incidence_eq := by
    intro obligation event
    cases event
    rfl
  boundaryDisposition := boundaryDisposition
  ReopenEvent := fun _ => Empty
  reopenPayload := fun event => nomatch event

abbrev P := process

def responsibilitySource : ResponsibilityState V where
  slots := [.live sourceObligation]
  history := []

def responsibilitySlot : Fin responsibilitySource.slots.length :=
  ⟨0, by decide⟩

theorem responsibilitySlot_present :
    responsibilitySource.slots.get responsibilitySlot =
      .live sourceObligation :=
  rfl

def successionEdge : P.Edge responsibilitySource :=
  .cross responsibilitySlot sourceObligation responsibilitySlot_present
    .succession

def exactSuccession : ExactSuccessionAt P successionEdge :=
  (ExactSuccessionAt.compile successionEdge).get (by rfl)

@[simp] theorem exactSuccession_oldObligation :
    exactSuccession.oldObligation = sourceObligation :=
  rfl

@[simp] theorem exactSuccession_nextObligation :
    exactSuccession.nextObligation = acceptedTransferCarry.target :=
  rfl

@[simp] theorem exactSuccession_sourceEvent :
    exactSuccession.sourceEvent = EventState.after :=
  rfl

def incidenceCompiler : ActorResponsibilityIncidenceCompiler core V where
  SourceSeed := Unit
  sourceAdmittedAt := fun _ => True
  sourceActorSeed := fun _ => .s5
  sourceActor_active := by
    intro seed admitted
    rfl
  sourceObligation := fun _ => sourceObligation
  sourceEvent := fun _ => .after
  TargetSeed := Unit
  targetAdmittedAt := fun _ => True
  targetActorSeed := fun _ => .t4
  targetActor_active := by
    intro seed admitted
    rfl
  targetObligation := fun _ => acceptedTransferCarry.target
  targetEvent := fun _ => .after
  HistoricalSeed := Empty
  historicalAdmittedAt := fun seed => nomatch seed
  historicalActorSeed := fun seed => nomatch seed
  historicalActorState := fun seed => nomatch seed
  historicalActor_active := by
    intro seed
    exact nomatch seed
  historicalObligation := fun seed => nomatch seed
  historicalEvent := fun seed => nomatch seed

def sourceIncidenceSeed : incidenceCompiler.ExactSourceSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def targetIncidenceSeed : incidenceCompiler.ExactTargetSeed :=
  ⟨(), .after, by simp [actualEventOccurrenceOf], rfl, trivial⟩

def sourceResponsibility : incidenceCompiler.SourceResponsibilityAt
    (sourceActor .s5) sourceObligation .after where
  seed := sourceIncidenceSeed
  actor_eq := rfl
  obligation_eq := rfl
  sourceEvent_eq := rfl

def targetResponsibility : incidenceCompiler.TargetResponsibilityAt
    (targetActor .t4) acceptedTransferCarry.target .after where
  seed := targetIncidenceSeed
  actor_eq := rfl
  obligation_eq := rfl
  sourceEvent_eq := rfl

def incidence : ActorResponsibilityIncidence core V where
  compiler := incidenceCompiler
  source_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    calc
      first = firstAt.seed.actor incidenceCompiler := firstAt.actor_eq.symm
      _ = lastAt.seed.actor incidenceCompiler := by
        apply Subtype.ext
        rfl
      _ = last := lastAt.actor_eq
  target_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    calc
      first = firstAt.seed.actor incidenceCompiler := firstAt.actor_eq.symm
      _ = lastAt.seed.actor incidenceCompiler := by
        apply Subtype.ext
        rfl
      _ = last := lastAt.actor_eq
  historical_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    exact nomatch firstAt.seed.1

def successionAuthority : ExactSuccessionAuthority core P incidence
    (sourceActor .s5) (targetActor .t4) where
  sourceState := responsibilitySource
  edge := successionEdge
  framework := exactSuccession
  sourceResponsibility := by simpa [incidence] using sourceResponsibility
  targetResponsibility := by simpa [incidence] using targetResponsibility
  notIdentity := by
    intro identity
    have actorEq := identity.source_eq
    have values := congrArg Subtype.val actorEq
    cases values

def installation : FrameworkInstallation core :=
  .installed V P incidence

def method : SourceOwnedLifecycleAuthorityMethod core where
  installation := installation

@[simp] theorem method_installation : method.installation = installation :=
  rfl

private theorem singleton_not_split {source : core.SourceActor}
    {target : core.TargetActor}
    (singleton : core.SingletonDescendantAt source target) :
    ¬ core.SplitAt source := by
  rintro ⟨left, right, leftLink, rightLink, different⟩
  have leftEq := singleton.2 left leftLink
  have rightEq := singleton.2 right rightLink
  exact different (leftEq.trans rightEq.symm)

theorem singletonCompiler_nonempty
    (source : core.SourceActor) (target : core.TargetActor)
    (descendants : core.SingletonDescendantAt source target)
    (_predecessors : core.SingletonPredecessorAt source target) :
    Nonempty (core.DomainIdentityTransportAt source target ⊕
      InstalledSuccessionAt installation source target) := by
  have admitted := (actorRelated_iff source target).mp descendants.1
  rcases eventTransfers_cases source.1 target.1 admitted with
    stable | grid | succession
  · rcases stable with ⟨sourceValue, targetValue⟩
    have sourceEq : source = sourceActor .s0 := Subtype.ext sourceValue
    have targetEq : target = targetActor .t0 := Subtype.ext targetValue
    rw [sourceEq, targetEq]
    exact ⟨.inl identityAuthority⟩
  · have notSplit := singleton_not_split descendants
    rcases grid.1 with sourceValue | sourceValue | sourceValue
    · have sourceEq : source = sourceActor .s1 := Subtype.ext sourceValue
      rw [sourceEq] at notSplit
      exact (notSplit split_s1).elim
    · have sourceEq : source = sourceActor .s2 := Subtype.ext sourceValue
      rw [sourceEq] at notSplit
      exact (notSplit split_s2).elim
    · have sourceEq : source = sourceActor .s3 := Subtype.ext sourceValue
      rw [sourceEq] at notSplit
      exact (notSplit split_s3).elim
  · rcases succession with ⟨sourceValue, targetValue⟩
    have sourceEq : source = sourceActor .s5 := Subtype.ext sourceValue
    have targetEq : target = targetActor .t4 := Subtype.ext targetValue
    rw [sourceEq, targetEq]
    exact ⟨.inr successionAuthority⟩

noncomputable def singletonCompiler
    (source : core.SourceActor) (target : core.TargetActor)
    (descendants : core.SingletonDescendantAt source target)
    (predecessors : core.SingletonPredecessorAt source target) :
    core.DomainIdentityTransportAt source target ⊕
      InstalledSuccessionAt installation source target :=
  Classical.choice
    (singletonCompiler_nonempty source target descendants predecessors)

private theorem target_eq_t5_of_empty (target : core.TargetActor)
    (empty : core.EmptyPredecessorAt target) : target = targetActor .t5 := by
  apply Subtype.ext
  cases targetValue : target.1
  · exact (empty (sourceActor .s0)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, targetValue]))).elim
  · exact (empty (sourceActor .s1)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, targetValue]))).elim
  · exact (empty (sourceActor .s1)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, targetValue]))).elim
  · exact (empty (sourceActor .s2)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, targetValue]))).elim
  · exact (empty (sourceActor .s5)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, targetValue]))).elim
  · rfl

def emptyTargetCompiler (target : core.TargetActor)
    (empty : core.EmptyPredecessorAt target) :
    FreshOriginAuthority installation target ⊕
      ReappearanceAuthority installation target := by
  have targetEq := target_eq_t5_of_empty target empty
  rw [targetEq]
  exact .inl (.inl {
    origin := freshAuthority
    noHistoricalIdentity := by
      intro historical reappearance
      exact nomatch reappearance.reappearance.1 })

private theorem source_eq_s4_of_empty (source : core.SourceActor)
    (empty : core.ExitAt source) : source = sourceActor .s4 := by
  apply Subtype.ext
  cases sourceValue : source.1
  · exact (empty (targetActor .t0)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, sourceValue]))).elim
  · exact (empty (targetActor .t1)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, sourceValue]))).elim
  · exact (empty (targetActor .t1)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, sourceValue]))).elim
  · exact (empty (targetActor .t1)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, sourceValue]))).elim
  · rfl
  · exact (empty (targetActor .t4)
      ((actorRelated_iff _ _).2 (by simp [eventTransfers, sourceValue]))).elim

def emptySourceCompiler (source : core.SourceActor) (empty : core.ExitAt source) :
    ExitAuthority installation source := by
  have sourceEq := source_eq_s4_of_empty source empty
  rw [sourceEq]
  exact .inl exitAuthority

theorem singletonCoverage : ∀ source target,
    core.SingletonDescendantAt source target →
    core.SingletonPredecessorAt source target →
      Nonempty (core.DomainIdentityTransportAt source target ⊕
        InstalledSuccessionAt installation source target) :=
  singletonCompiler_nonempty

theorem emptyTargetCoverage : ∀ target,
    core.EmptyPredecessorAt target →
      Nonempty (FreshOriginAuthority installation target ⊕
        ReappearanceAuthority installation target) :=
  fun target empty => ⟨emptyTargetCompiler target empty⟩

theorem emptySourceCoverage : ∀ source,
    core.ExitAt source → Nonempty (ExitAuthority installation source) :=
  fun source empty => ⟨emptySourceCompiler source empty⟩

theorem compile?_isSome :
    (SourceOwnedActorLifecycleLaw.compile? method).isSome := by
  apply (SourceOwnedActorLifecycleLaw.compile?_isSome_iff method).2
  exact ⟨singletonCoverage, emptyTargetCoverage, emptySourceCoverage⟩

noncomputable def law : SourceOwnedActorLifecycleLaw core :=
  (SourceOwnedActorLifecycleLaw.compile? method).get compile?_isSome

@[simp] theorem law_method : law.method = method :=
  SourceOwnedActorLifecycleLaw.compile?_get_method method compile?_isSome

@[simp] theorem law_installation : law.method.installation = installation := by
  calc
    law.method.installation = method.installation :=
      congrArg SourceOwnedLifecycleAuthorityMethod.installation law_method
    _ = installation := method_installation

end FixedAdapter
end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
