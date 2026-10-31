import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization

/-!
# M7 preference readouts and the hidden-fibre control

The social-choice bridges use arbitrary agent and alternative types.  Their
standard axioms live entirely on visible preference profiles and visible
collective outputs.  This module supplies a uniform hidden occurrence fibre
on which every such readout is unchanged while authority differs.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace SocialChoice
namespace M7

open Observer

universe uAgent uAlternative uVisible uHidden uResidual uReadout

/-- A complete and transitive weak preference relation.  Rationality is part
of the value type rather than a later premise on a social rule. -/
structure WeakPreference (Alternative : Type uAlternative) where
  ranks : Alternative → Alternative → Prop
  reflexive : ∀ alternative, ranks alternative alternative
  complete : ∀ left right, ranks left right ∨ ranks right left
  transitive : ∀ {first second third},
    ranks first second → ranks second third → ranks first third

namespace WeakPreference

variable {Alternative : Type uAlternative}

/-- Strict preference derived from the weak relation. -/
def Strict (preference : WeakPreference Alternative)
    (left right : Alternative) : Prop :=
  preference.ranks left right ∧ ¬ preference.ranks right left

end WeakPreference

/-- A weak-preference profile over arbitrary agent and alternative types. -/
abbrev PreferenceProfile
    (Agent : Type uAgent) (Alternative : Type uAlternative) :=
  Agent → WeakPreference Alternative

/-- A complete, transitive, antisymmetric weak order.  Antisymmetry removes
ties between distinct alternatives, so profiles of these values form the
strict/linear domain used by the Gibbard--Satterthwaite bridge. -/
structure LinearPreference (Alternative : Type uAlternative)
    extends WeakPreference Alternative where
  antisymmetric : ∀ {left right},
    ranks left right → ranks right left → left = right

namespace LinearPreference

variable {Alternative : Type uAlternative}

def Strict (preference : LinearPreference Alternative)
    (left right : Alternative) : Prop :=
  WeakPreference.Strict preference.toWeakPreference left right

end LinearPreference

/-- A strict/linear preference profile with no fixed agent or alternative
cardinality. -/
abbrev LinearPreferenceProfile
    (Agent : Type uAgent) (Alternative : Type uAlternative) :=
  Agent → LinearPreference Alternative

/-- Universe-polymorphic source data for a hidden occurrence coordinate.  Its
automorphism must commute with the hidden authority readout and change the
authority value at every hidden point. -/
structure HiddenFibreExtension
    (Hidden : Type uHidden) (Residual : Type uResidual) where
  authorityReadout : Hidden → Residual
  hiddenEquiv : Hidden ≃ Hidden
  authorityEquiv : Residual ≃ Residual
  anchorHidden : Hidden
  authority_commutes : ∀ hidden,
    authorityReadout (hiddenEquiv hidden) =
      authorityEquiv (authorityReadout hidden)
  changesAuthority : ∀ hidden,
    authorityEquiv (authorityReadout hidden) ≠ authorityReadout hidden

namespace HiddenFibreExtension

variable {Visible : Type uVisible}
variable {Hidden : Type uHidden}
variable {Residual : Type uResidual}

/-- Projection observer for an arbitrary hidden carrier. -/
def observer (extension : HiddenFibreExtension Hidden Residual) :
    AuthorityObserver (Visible × Hidden) Visible Residual where
  forget := Prod.fst
  authorityK := fun occurrence => extension.authorityReadout occurrence.2

def occurrenceEquiv (extension : HiddenFibreExtension Hidden Residual) :
    (Visible × Hidden) ≃ (Visible × Hidden) :=
  Equiv.prodCongr (Equiv.refl Visible) extension.hiddenEquiv

/-- The arbitrary hidden symmetry is a genuine observer automorphism. -/
def automorphism (extension : HiddenFibreExtension Hidden Residual) :
    AdmissibleObserverAutomorphism
      (observer (Visible := Visible) extension) where
  occurrenceEquiv := occurrenceEquiv extension
  visibleEquiv := Equiv.refl Visible
  authorityEquiv := extension.authorityEquiv
  forget_commutes := by
    intro occurrence
    rfl
  authority_commutes := by
    intro occurrence
    exact extension.authority_commutes occurrence.2

/-- Every visible point is reachable through the source-owned hidden anchor,
and the whole hidden fibre changes authority. -/
def vertical (extension : HiddenFibreExtension Hidden Residual)
    (visible : Visible) :
    AuthorityChangingVerticalAutomorphism
      (observer (Visible := Visible) extension) where
  automorphism := automorphism extension
  anchor := visible
  anchorOccurrence := (visible, extension.anchorHidden)
  anchor_reachable := rfl
  fixesVisible := rfl
  changesAuthorityOnFiber := by
    intro occurrence _inFiber
    exact extension.changesAuthority occurrence.2

/-- Canonical M6 boundary generated over any visible point and arbitrary
hidden authority carrier. -/
def attachment (extension : HiddenFibreExtension Hidden Residual)
    (visible : Visible) :
    SourceGeneratedObserverAttachingDirectionAt
      (rootedObserverObstruction (vertical extension visible)) :=
  canonicalObserverObstructionDirection (vertical extension visible)

/-- Pull any visible readout back along projection without granting access to
the hidden coordinate. -/
def pullback {Readout : Type uReadout} (readout : Visible → Readout) :
    Visible × Hidden → Readout :=
  fun occurrence => readout occurrence.1

/-- Every visible readout is invariant across arbitrary points of one hidden
fibre. -/
@[simp] theorem pullback_eq_on_fibre
    {Readout : Type uReadout} (readout : Visible → Readout)
    (visible : Visible) (firstHidden secondHidden : Hidden) :
    pullback readout (visible, firstHidden) =
      pullback readout (visible, secondHidden) :=
  rfl

/-- The generated boundary, rather than a caller-supplied pair, rejects
visible-only authority factorization for every such hidden extension. -/
theorem attachment_noAuthorityFactorization
    (extension : HiddenFibreExtension Hidden Residual)
    (visible : Visible) :
    ¬ Nonempty (AuthorityFactorization
      (observer (Visible := Visible) extension)) :=
  (attachment extension visible).boundary_noAuthorityFactorization

end HiddenFibreExtension

end M7
end SocialChoice
end Society
end ProcessGame
end SaturationMonoid
