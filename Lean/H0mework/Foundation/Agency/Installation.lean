import H0mework.Foundation.Agency.LifecycleAuthority

/-!
# Optional shared responsibility-framework installation

A lifecycle law either has no responsibility ontology or one shared exact
`(V,P,incidence)` installation.  All framework branches factor through it.
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

/-! ## Optional shared framework installation -/

/-- One law either uses no responsibility ontology or one shared, already
installed `(V,P,incidence)`.  Branches cannot mix processes. -/
inductive FrameworkInstallation
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
  | absent
  | installed (V : Vocabulary.{x}) (P : NativeResponsibilityProcess V)
      (incidence : ActorResponsibilityIncidence core V)

def InstalledSuccessionAt
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (source : core.SourceActor) (target : core.TargetActor) :
    Type (max w x) :=
  match installation with
  | .absent => ULift.{max w x, 0} Empty
  | .installed _ P incidence =>
      ExactSuccessionAuthority core P incidence source target

def InstalledFreshOriginAt
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (target : core.TargetActor) : Type (max w x) :=
  match installation with
  | .absent => ULift.{max w x, 0} Empty
  | .installed _ P incidence =>
      ExactFreshOriginAuthority core P incidence target

def InstalledReappearanceAt
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (target : core.TargetActor) : Type (max w x) :=
  match installation with
  | .absent => ULift.{max w x, 0} Empty
  | .installed _ P incidence =>
      ExactReappearanceAuthority core P incidence target

def InstalledExitAt
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (source : core.SourceActor) : Type (max w x) :=
  match installation with
  | .absent => ULift.{max w x, 0} Empty
  | .installed _ P incidence =>
      ExactFinalExitAuthority core P incidence source

abbrev FreshOriginAuthority
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (target : core.TargetActor) :=
  DomainFreshOriginAuthority core target ⊕
    InstalledFreshOriginAt installation target

abbrev ReappearanceAuthority
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (target : core.TargetActor) :=
  DomainReappearanceAuthority core target ⊕
    InstalledReappearanceAt installation target

abbrev ExitAuthority
    (installation : FrameworkInstallation.{u, v, w, x} core)
    (source : core.SourceActor) :=
  core.DomainExitAuthorityAt source ⊕ InstalledExitAt installation source

def InstalledSuccessionHasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {source : core.SourceActor} {target : core.TargetActor}
    (authority : InstalledSuccessionAt installation source target) : Prop :=
  match installation with
  | .absent => False
  | .installed _ _ _ =>
      SameDebtLineage authority.framework.oldObligation
        authority.framework.nextObligation ∧
      (core.DomainIdentityTransportAt source target → False)

theorem installedSuccession_hasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {source : core.SourceActor} {target : core.TargetActor}
    (authority : InstalledSuccessionAt installation source target) :
    InstalledSuccessionHasExactProvenance installation authority := by
  cases installation with
  | absent => exact nomatch authority.down
  | installed V P incidence =>
      exact ⟨authority.sameDebtLineage, authority.notIdentity⟩

def FreshOriginHasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {target : core.TargetActor}
    (authority : FreshOriginAuthority installation target) : Prop :=
  match authority with
  | .inl _domain => Nonempty (core.DomainFreshOriginAt target)
  | .inr framework =>
      match installation with
      | .absent => False
      | .installed _ P _ =>
          ResponsibilityState.FreshlyAllocatedAt framework.sourceState
            framework.edge.target (framework.admission.slot P)

theorem freshOrigin_hasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {target : core.TargetActor}
    (authority : FreshOriginAuthority installation target) :
    FreshOriginHasExactProvenance installation authority := by
  cases authority with
  | inl domain => exact ⟨domain.origin⟩
  | inr framework =>
      cases installation with
      | absent => exact nomatch framework.down
      | installed V P incidence => exact framework.freshlyAllocated

def ReappearanceHasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {target : core.TargetActor}
    (authority : ReappearanceAuthority installation target) : Prop :=
  match authority with
  | .inl domain => Nonempty (core.DomainReappearanceAt domain.historical target)
  | .inr framework =>
      match installation with
      | .absent => False
      | .installed _ P _ =>
          SameDebtLineage framework.reopen.archive.obligation
            (framework.reopen.targetObligation P)

theorem reappearance_hasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {target : core.TargetActor}
    (authority : ReappearanceAuthority installation target) :
    ReappearanceHasExactProvenance installation authority := by
  cases authority with
  | inl domain => exact ⟨domain.exactOrigin⟩
  | inr framework =>
      cases installation with
      | absent => exact nomatch framework.down
      | installed V P incidence => exact framework.sameDebtLineage

def ExitHasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {source : core.SourceActor}
    (authority : ExitAuthority installation source) : Prop :=
  match authority with
  | .inl _domain => Nonempty (core.DomainExitAuthorityAt source)
  | .inr framework =>
      match installation with
      | .absent => False
      | .installed _ P _ =>
          ResponsibilityState.DisappearsAt framework.sourceState
            framework.edge.target (framework.exit.slot P)

theorem exit_hasExactProvenance
    (installation : FrameworkInstallation.{u, v, w, x} core)
    {source : core.SourceActor}
    (authority : ExitAuthority installation source) :
    ExitHasExactProvenance installation authority := by
  cases authority with
  | inl domain => exact ⟨domain⟩
  | inr framework =>
      cases installation with
      | absent => exact nomatch framework.down
      | installed V P incidence => exact framework.disappears

end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
