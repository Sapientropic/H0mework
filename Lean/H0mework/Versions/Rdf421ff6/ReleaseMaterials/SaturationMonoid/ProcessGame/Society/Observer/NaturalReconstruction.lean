import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver
import Mathlib.Logic.Equiv.Basic

/-!
# Natural reconstruction under observer automorphisms

This module strengthens a surrogate right section by requiring equivariance
under every admissible automorphism of the observer.  A vertical automorphism
which fixes a reachable visible point but changes authority throughout its
fibre has no natural choice of representative.

The proof has two independent steps: authority commutation first shows that
the occurrence automorphism has no fixed point in the fibre; section
naturality then forces its chosen representative to be fixed.  Thus the
result is a genuine natural-section obstruction, not a renamed left-inverse
failure.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Observer

universe uOccurrence uVisible uResidual

variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Residual : Type uResidual}

/-- An admissible symmetry of an authority observer.  All three coordinates
are equivalences, and both observer squares commute on every actual
occurrence. -/
structure AdmissibleObserverAutomorphism
    (O : AuthorityObserver Occurrence Visible Residual) where
  occurrenceEquiv : Occurrence ≃ Occurrence
  visibleEquiv : Visible ≃ Visible
  authorityEquiv : Residual ≃ Residual
  forget_commutes : ∀ occurrence,
    O.forget (occurrenceEquiv occurrence) =
      visibleEquiv (O.forget occurrence)
  authority_commutes : ∀ occurrence,
    O.authorityK (occurrenceEquiv occurrence) =
      authorityEquiv (O.authorityK occurrence)

namespace AdmissibleObserverAutomorphism

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- The identity symmetry is always admissible. -/
def refl : AdmissibleObserverAutomorphism O where
  occurrenceEquiv := Equiv.refl _
  visibleEquiv := Equiv.refl _
  authorityEquiv := Equiv.refl _
  forget_commutes := fun _ => rfl
  authority_commutes := fun _ => rfl

end AdmissibleObserverAutomorphism

/-- A surrogate section natural under every admissible observer automorphism.
Authority equivariance is an explicit field of the structure contract; it is
not supplied later as a theorem premise. -/
structure NaturalSurrogateSection
    (O : AuthorityObserver Occurrence Visible Residual)
    extends SurrogateRightSection O where
  naturality : ∀ automorphism : AdmissibleObserverAutomorphism O,
    ∀ visible,
      lift (automorphism.visibleEquiv visible) =
        automorphism.occurrenceEquiv (lift visible)
  preservesAuthority : ∀ automorphism : AdmissibleObserverAutomorphism O,
    ∀ visible,
      O.authorityK (lift (automorphism.visibleEquiv visible)) =
        automorphism.authorityEquiv (O.authorityK (lift visible))

/-- Compatibility alias emphasizing that this is still a right section, not
an occurrence-valued left inverse. -/
abbrev NaturalSurrogateRightSection
    (O : AuthorityObserver Occurrence Visible Residual) :=
  NaturalSurrogateSection O

/-- The full reconstruction claim combines natural representative choice,
visible factorization of actual authority, and recovery of every occurrence.
All semantic obligations are fields of the reconstruction itself. -/
structure NaturalAuthorityReconstruction
    (O : AuthorityObserver Occurrence Visible Residual)
    extends NaturalSurrogateSection O where
  readAuthority : Visible → Residual
  preservesActualAuthority : ∀ occurrence,
    readAuthority (O.forget occurrence) = O.authorityK occurrence
  recoversOccurrence : Function.LeftInverse lift O.forget

namespace NaturalAuthorityReconstruction

variable {O : AuthorityObserver Occurrence Visible Residual}

def toAuthorityFactorization
    (reconstruction : NaturalAuthorityReconstruction O) :
    AuthorityFactorization O where
  readAuthority := reconstruction.readAuthority
  preservesActualAuthority := reconstruction.preservesActualAuthority

def toFaithfulAuthorityReconstruction
    (reconstruction : NaturalAuthorityReconstruction O) :
    FaithfulAuthorityReconstruction O where
  lift := reconstruction.lift
  lift_forget := reconstruction.lift_forget
  readAuthority := reconstruction.readAuthority
  preservesActualAuthority := reconstruction.preservesActualAuthority
  recoversOccurrence := reconstruction.recoversOccurrence

end NaturalAuthorityReconstruction

namespace AuthorityKernelPair

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- Pair-level authority loss already rules out the full natural
reconstruction contract, independently of which automorphisms are present. -/
theorem noNaturalAuthorityReconstruction
    (pair : AuthorityKernelPair O) :
    ¬ Nonempty (NaturalAuthorityReconstruction O) := by
  rintro ⟨reconstruction⟩
  exact pair.noAuthorityFactorization
    ⟨reconstruction.toAuthorityFactorization⟩

end AuthorityKernelPair

/-- A genuinely fibre-moving vertical automorphism at an explicitly reachable
visible point. -/
structure FibreMovingVerticalAutomorphism
    (O : AuthorityObserver Occurrence Visible Residual) where
  automorphism : AdmissibleObserverAutomorphism O
  anchor : Visible
  anchorOccurrence : Occurrence
  anchor_reachable : O.forget anchorOccurrence = anchor
  fixesVisible : automorphism.visibleEquiv anchor = anchor
  movesOccurrenceOnFiber : ∀ occurrence,
    O.forget occurrence = anchor →
      automorphism.occurrenceEquiv occurrence ≠ occurrence

/-- A vertical automorphism whose authority coordinate changes every actual
authority value above one explicitly reachable fixed visible point. -/
structure AuthorityChangingVerticalAutomorphism
    (O : AuthorityObserver Occurrence Visible Residual) where
  automorphism : AdmissibleObserverAutomorphism O
  anchor : Visible
  anchorOccurrence : Occurrence
  anchor_reachable : O.forget anchorOccurrence = anchor
  fixesVisible : automorphism.visibleEquiv anchor = anchor
  changesAuthorityOnFiber : ∀ occurrence,
    O.forget occurrence = anchor →
      automorphism.authorityEquiv (O.authorityK occurrence) ≠
        O.authorityK occurrence

namespace AuthorityChangingVerticalAutomorphism

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- Exact `K` commutation turns authority change into fixed-point-free motion
of every occurrence in the anchored fibre. -/
theorem occurrenceEquiv_ne_on_fiber
    (vertical : AuthorityChangingVerticalAutomorphism O)
    (occurrence : Occurrence)
    (inFiber : O.forget occurrence = vertical.anchor) :
    vertical.automorphism.occurrenceEquiv occurrence ≠ occurrence := by
  intro fixedOccurrence
  apply vertical.changesAuthorityOnFiber occurrence inFiber
  calc
    vertical.automorphism.authorityEquiv (O.authorityK occurrence) =
        O.authorityK (vertical.automorphism.occurrenceEquiv occurrence) :=
      (vertical.automorphism.authority_commutes occurrence).symm
    _ = O.authorityK occurrence := congrArg O.authorityK fixedOccurrence

/-- Forget authority values after using them to derive the stronger geometric
fact that the vertical automorphism moves every occurrence in the fibre. -/
def toFibreMoving
    (vertical : AuthorityChangingVerticalAutomorphism O) :
    FibreMovingVerticalAutomorphism O where
  automorphism := vertical.automorphism
  anchor := vertical.anchor
  anchorOccurrence := vertical.anchorOccurrence
  anchor_reachable := vertical.anchor_reachable
  fixesVisible := vertical.fixesVisible
  movesOccurrenceOnFiber := vertical.occurrenceEquiv_ne_on_fiber

end AuthorityChangingVerticalAutomorphism

namespace FibreMovingVerticalAutomorphism

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- A natural surrogate section cannot choose a representative in a reachable
fibre moved vertically by an admissible automorphism.  The contradiction uses
the section's naturality field directly. -/
theorem noNaturalSurrogateSection
    (vertical : FibreMovingVerticalAutomorphism O) :
    ¬ Nonempty (NaturalSurrogateSection O) := by
  rintro ⟨naturalSection⟩
  let chosen := naturalSection.lift vertical.anchor
  have chosenInFiber : O.forget chosen = vertical.anchor :=
    naturalSection.lift_forget vertical.anchor
  have chosenMoves :
      vertical.automorphism.occurrenceEquiv chosen ≠ chosen :=
    vertical.movesOccurrenceOnFiber chosen chosenInFiber
  apply chosenMoves
  have naturalityAtAnchor :=
    naturalSection.naturality vertical.automorphism vertical.anchor
  rw [vertical.fixesVisible] at naturalityAtAnchor
  exact naturalityAtAnchor.symm

/-- The stronger natural authority reconstruction is also impossible. -/
theorem noNaturalAuthorityReconstruction
    (vertical : FibreMovingVerticalAutomorphism O) :
    ¬ Nonempty (NaturalAuthorityReconstruction O) := by
  rintro ⟨reconstruction⟩
  exact vertical.noNaturalSurrogateSection
    ⟨reconstruction.toNaturalSurrogateSection⟩

end FibreMovingVerticalAutomorphism

namespace AuthorityChangingVerticalAutomorphism

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- Strong authority-changing vertical obstruction to a genuinely natural
surrogate section.  `toFibreMoving` consumes `K` commutation; the downstream
no-go consumes section naturality. -/
theorem noNaturalSurrogateSection
    (vertical : AuthorityChangingVerticalAutomorphism O) :
    ¬ Nonempty (NaturalSurrogateSection O) :=
  vertical.toFibreMoving.noNaturalSurrogateSection

theorem noNaturalAuthorityReconstruction
    (vertical : AuthorityChangingVerticalAutomorphism O) :
    ¬ Nonempty (NaturalAuthorityReconstruction O) :=
  vertical.toFibreMoving.noNaturalAuthorityReconstruction

end AuthorityChangingVerticalAutomorphism

end Observer
end Society
end ProcessGame
end SaturationMonoid
