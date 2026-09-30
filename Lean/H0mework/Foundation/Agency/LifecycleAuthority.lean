import H0mework.Foundation.Agency.LifecycleSeeds
import H0mework.Foundation.Agency.ResponsibilityIncidence
import H0mework.Foundation.Agency.Succession
import H0mework.Foundation.Agency.OriginExit

/-!
# Exact actor lifecycle authorities

Framework and domain lifecycle authorities aligned with exact generated
actors and exact responsibility-incidence seeds.
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

/-! ## Exact framework authority packages -/

structure ExactSuccessionAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (source : core.SourceActor) (target : core.TargetActor) where
  sourceState : ResponsibilityState V
  edge : P.Edge sourceState
  framework : ExactSuccessionAt P edge
  sourceResponsibility : incidence.SourceResponsibilityAt source
    framework.oldObligation framework.sourceEvent
  targetResponsibility : incidence.TargetResponsibilityAt target
    framework.nextObligation framework.sourceEvent
  notIdentity : core.DomainIdentityTransportAt source target → False

namespace ExactSuccessionAuthority

theorem sameDebtLineage
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {source : core.SourceActor} {target : core.TargetActor}
    (authority : ExactSuccessionAuthority core P incidence source target) :
    SameDebtLineage authority.framework.oldObligation
      authority.framework.nextObligation :=
  authority.framework.sameDebtLineage

end ExactSuccessionAuthority

structure ExactFreshOriginAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (target : core.TargetActor) where
  sourceState : ResponsibilityState V
  edge : P.Edge sourceState
  admission : FreshAdmissionEdge P edge
  targetResponsibility : incidence.TargetResponsibilityAt target
    (admission.targetObligation P)
    (admission.targetObligation P).admission.sourceEvent
  noHistoricalIdentity : ∀ historical,
    core.DomainReappearanceAt historical target → False

namespace ExactFreshOriginAuthority

theorem freshlyAllocated
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {target : core.TargetActor}
    (authority : ExactFreshOriginAuthority core P incidence target) :
    ResponsibilityState.FreshlyAllocatedAt authority.sourceState
      authority.edge.target (authority.admission.slot P) :=
  authority.admission.freshlyAllocated P

end ExactFreshOriginAuthority

/-- Domain-native fresh origin, such as an exact played-point or biological
birth seed, together with the absence of any transported historical actor. -/
structure DomainFreshOriginAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (target : core.TargetActor) where
  origin : core.DomainFreshOriginAt target
  noHistoricalIdentity : ∀ historical,
    core.DomainReappearanceAt historical target → False

namespace DomainFreshOriginAuthority

def exactOrigin
    {target : core.TargetActor}
    (authority : DomainFreshOriginAuthority core target) :
    core.DomainFreshOriginAt target :=
  authority.origin

end DomainFreshOriginAuthority

abbrev InstalledFreshOriginAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (target : core.TargetActor) :=
  DomainFreshOriginAuthority core target ⊕
    ExactFreshOriginAuthority core P incidence target

structure ExactReappearanceAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (target : core.TargetActor) where
  historical : core.HistoricalActorBefore
  historicalIdentity :
    core.DomainReappearanceAt historical target
  sourceState : ResponsibilityState V
  edge : P.Edge sourceState
  reopen : ReopenEdge P edge
  historicalResponsibility : incidence.HistoricalResponsibilityAt historical
    reopen.archive.obligation (P.reopenPayload reopen.event).sourceEvent
  targetResponsibility : incidence.TargetResponsibilityAt target
    (reopen.targetObligation P) (P.reopenPayload reopen.event).sourceEvent

namespace ExactReappearanceAuthority

theorem sameDebtLineage
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {target : core.TargetActor}
    (authority : ExactReappearanceAuthority core P incidence target) :
    SameDebtLineage authority.reopen.archive.obligation
      (authority.reopen.targetObligation P) :=
  authority.reopen.sameDebtLineage P

end ExactReappearanceAuthority

/-- Domain-native reopening/reappearance carried by an exact domain event
and an exact historical identity transport. -/
structure DomainReappearanceAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (target : core.TargetActor) where
  historical : core.HistoricalActorBefore
  origin : core.DomainReappearanceAt historical target

namespace DomainReappearanceAuthority

def exactOrigin
    {target : core.TargetActor}
    (authority : DomainReappearanceAuthority core target) :
    core.DomainReappearanceAt authority.historical target :=
  authority.origin

end DomainReappearanceAuthority

abbrev InstalledReappearanceAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (target : core.TargetActor) :=
  DomainReappearanceAuthority core target ⊕
    ExactReappearanceAuthority core P incidence target

structure ExactFinalExitAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (source : core.SourceActor) where
  sourceState : ResponsibilityState V
  edge : P.Edge sourceState
  exit : FinalExitEdge P edge
  sourceResponsibility : incidence.SourceResponsibilityAt source exit.obligation
    (P.boundarySource exit.event)

namespace ExactFinalExitAuthority

theorem disappears
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {source : core.SourceActor}
    (authority : ExactFinalExitAuthority core P incidence source) :
    ResponsibilityState.DisappearsAt authority.sourceState
      authority.edge.target (authority.exit.slot P) :=
  authority.exit.disappears P

end ExactFinalExitAuthority

/-- Exit may be generated either by a domain-native terminal/capture event or
by the exact final edge of the installed responsibility process. -/
abbrev InstalledExitAuthority
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    {V : Vocabulary.{x}} (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (source : core.SourceActor) :=
  core.DomainExitAuthorityAt source ⊕
    ExactFinalExitAuthority core P incidence source

/-- Domain/framework fresh origins both expose exact generated provenance. -/
theorem installedFreshOriginAuthority_exact
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {target : core.TargetActor}
    (authority : InstalledFreshOriginAuthority core P incidence target) :
    Nonempty (core.DomainFreshOriginAt target) ∨
      ∃ framework : ExactFreshOriginAuthority core P incidence target,
        ResponsibilityState.FreshlyAllocatedAt framework.sourceState
          framework.edge.target (framework.admission.slot P) := by
  cases authority with
  | inl domain => exact Or.inl ⟨domain.exactOrigin⟩
  | inr framework => exact Or.inr ⟨framework, framework.freshlyAllocated⟩

/-- Domain/framework reappearances both expose exact historical provenance;
the framework branch additionally consumes the existing reopen lineage law. -/
theorem installedReappearanceAuthority_exact
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {target : core.TargetActor}
    (authority : InstalledReappearanceAuthority core P incidence target) :
    (∃ domain : DomainReappearanceAuthority core target,
      authority = Sum.inl domain ∧
        Nonempty (core.DomainReappearanceAt domain.historical target)) ∨
      ∃ framework : ExactReappearanceAuthority core P incidence target,
        authority = Sum.inr framework ∧
          SameDebtLineage framework.reopen.archive.obligation
            (framework.reopen.targetObligation P) := by
  cases authority with
  | inl domain => exact Or.inl ⟨domain, rfl, ⟨domain.exactOrigin⟩⟩
  | inr framework =>
      exact Or.inr ⟨framework, rfl, framework.sameDebtLineage⟩

/-- Sparse omission is never an exit authority: the domain branch must
factor through an exact event seed and the framework branch must actually
generate disappearance. -/
theorem installedExitAuthority_exact
    {V : Vocabulary.{x}} {P : NativeResponsibilityProcess V}
    {incidence : ActorResponsibilityIncidence core V}
    {source : core.SourceActor}
    (authority : InstalledExitAuthority core P incidence source) :
    Nonempty (core.DomainExitAuthorityAt source) ∨
      ∃ framework : ExactFinalExitAuthority core P incidence source,
        ResponsibilityState.DisappearsAt framework.sourceState
          framework.edge.target (framework.exit.slot P) := by
  cases authority with
  | inl domain => exact Or.inl ⟨domain⟩
  | inr framework => exact Or.inr ⟨framework, framework.disappears⟩

end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
