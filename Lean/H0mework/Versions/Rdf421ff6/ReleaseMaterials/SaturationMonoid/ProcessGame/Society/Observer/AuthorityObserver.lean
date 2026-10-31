import Mathlib.Logic.Function.Basic

/-!
# Authority observers and reconstruction strength

An `AuthorityObserver` forgets an actual occurrence to a visible image while
retaining a source-native authority readout on the occurrence side.  The
interfaces below deliberately separate three logically different claims:

* a surrogate right section only chooses one preimage of each visible image;
* an authority factorization reads every actual authority value from the
  visible image;
* a faithful reconstruction additionally recovers every actual occurrence.

No finiteness, decidable equality, enumerability, or chosen calibration scope
is built into these definitions.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Observer

universe uOccurrence uVisible uResidual

/-- A visible observer of actual occurrences together with the authority
quantity which the visible image may fail to retain. -/
structure AuthorityObserver
    (Occurrence : Type uOccurrence)
    (Visible : Type uVisible)
    (Residual : Type uResidual) where
  forget : Occurrence → Visible
  authorityK : Occurrence → Residual

variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Residual : Type uResidual}

/-- Two different actual occurrences in one visible fibre whose independently
generated authority values differ.  The pair itself supplies a nonempty,
reachable fibre; no empty-domain no-go is possible. -/
structure AuthorityKernelPair
    (O : AuthorityObserver Occurrence Visible Residual) where
  left : Occurrence
  right : Occurrence
  occurrence_ne : left ≠ right
  visible_eq : O.forget left = O.forget right
  authority_ne : O.authorityK left ≠ O.authorityK right

/-- Object-level essential surjectivity produces at most this data: one
surrogate occurrence over each visible image.  It makes no claim that the
chosen occurrence is the actual occurrence which was forgotten. -/
structure SurrogateRightSection
    (O : AuthorityObserver Occurrence Visible Residual) where
  lift : Visible → Occurrence
  lift_forget : Function.RightInverse lift O.forget

namespace SurrogateRightSection

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- A supplied proof of surjectivity yields an ordinary surrogate section.
The choice is intentionally noncanonical and carries no occurrence or
authority-reconstruction claim. -/
noncomputable def ofSurjective
    (surjective : Function.Surjective O.forget) :
    SurrogateRightSection O where
  lift := fun visible => Classical.choose (surjective visible)
  lift_forget := fun visible => Classical.choose_spec (surjective visible)

/-- Ordinary right sections are exactly object-level surjectivity.  This
positive theorem is kept beside the no-go interfaces so that an authority
obstruction cannot be misread as a failure of essential surjectivity. -/
theorem nonempty_iff_surjective :
    Nonempty (SurrogateRightSection O) ↔ Function.Surjective O.forget := by
  constructor
  · rintro ⟨surrogate⟩ visible
    exact ⟨surrogate.lift visible, surrogate.lift_forget visible⟩
  · intro surjective
    exact ⟨ofSurjective surjective⟩

end SurrogateRightSection

/-- A proposed factorization of source-native authority through the visible
image.  This is already stronger than a surrogate right section and does not
need to choose occurrences. -/
structure AuthorityFactorization
    (O : AuthorityObserver Occurrence Visible Residual) where
  readAuthority : Visible → Residual
  preservesActualAuthority : ∀ occurrence,
    readAuthority (O.forget occurrence) = O.authorityK occurrence

/-- A reconstruction that both chooses a representative over every visible
image and recovers every actual occurrence.  Authority preservation is a
field of the reconstruction contract, not an auxiliary theorem premise. -/
structure FaithfulAuthorityReconstruction
    (O : AuthorityObserver Occurrence Visible Residual)
    extends SurrogateRightSection O where
  readAuthority : Visible → Residual
  preservesActualAuthority : ∀ occurrence,
    readAuthority (O.forget occurrence) = O.authorityK occurrence
  recoversOccurrence : Function.LeftInverse lift O.forget

namespace FaithfulAuthorityReconstruction

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- Forget the representative choice and retain the claimed visible authority
factorization. -/
def toAuthorityFactorization
    (reconstruction : FaithfulAuthorityReconstruction O) :
    AuthorityFactorization O where
  readAuthority := reconstruction.readAuthority
  preservesActualAuthority := reconstruction.preservesActualAuthority

end FaithfulAuthorityReconstruction

namespace AuthorityKernelPair

variable {O : AuthorityObserver Occurrence Visible Residual}

/-- A nontrivial authority fibre forbids every visible-only authority readout.
This is stronger than failure of an occurrence-valued left inverse. -/
theorem noAuthorityFactorization (pair : AuthorityKernelPair O) :
    ¬ Nonempty (AuthorityFactorization O) := by
  rintro ⟨factorization⟩
  apply pair.authority_ne
  calc
    O.authorityK pair.left =
        factorization.readAuthority (O.forget pair.left) :=
      (factorization.preservesActualAuthority pair.left).symm
    _ = factorization.readAuthority (O.forget pair.right) :=
      congrArg factorization.readAuthority pair.visible_eq
    _ = O.authorityK pair.right :=
      factorization.preservesActualAuthority pair.right

/-- The same exact pair generically forbids an occurrence-valued left inverse.
This theorem is separate from `noAuthorityFactorization`: loss of occurrence
identity and loss of authority are two independently inspectable failures. -/
theorem noOccurrenceLeftInverse (pair : AuthorityKernelPair O) :
    ¬ ∃ reconstruct : Visible → Occurrence,
      Function.LeftInverse reconstruct O.forget := by
  rintro ⟨reconstruct, recovers⟩
  apply pair.occurrence_ne
  calc
    pair.left = reconstruct (O.forget pair.left) :=
      (recovers pair.left).symm
    _ = reconstruct (O.forget pair.right) :=
      congrArg reconstruct pair.visible_eq
    _ = pair.right := recovers pair.right

/-- No faithful authority reconstruction exists over a nontrivial authority
fibre.  The proof consumes the stronger authority-factorization obstruction,
not merely injectivity of the forgetful map. -/
theorem noFaithfulAuthorityReconstruction
    (pair : AuthorityKernelPair O) :
    ¬ Nonempty (FaithfulAuthorityReconstruction O) := by
  rintro ⟨reconstruction⟩
  exact pair.noAuthorityFactorization
    ⟨reconstruction.toAuthorityFactorization⟩

end AuthorityKernelPair

end Observer
end Society
end ProcessGame
end SaturationMonoid
