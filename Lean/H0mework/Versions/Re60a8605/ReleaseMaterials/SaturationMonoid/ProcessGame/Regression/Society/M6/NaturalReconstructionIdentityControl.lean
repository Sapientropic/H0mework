import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.NaturalReconstruction

/-!
# M6 identity-observer positive control

The natural-reconstruction interface is not globally empty.  For an arbitrary
occurrence carrier, arbitrary residual carrier, and arbitrary source-native
authority map, the identity observer has a faithful natural reconstruction.
This generic control isolates the M6 no-go precisely to a nontrivial authority
fibre or an authority-changing vertical automorphism; it introduces no finite
calibration range.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M6NaturalReconstructionIdentityControl

open Observer

universe uOccurrence uResidual

variable {Occurrence : Type uOccurrence}
variable {Residual : Type uResidual}

def identityAuthorityObserver (authorityK : Occurrence → Residual) :
    AuthorityObserver Occurrence Occurrence Residual where
  forget := id
  authorityK := authorityK

def identityNaturalAuthorityReconstruction
    (authorityK : Occurrence → Residual) :
    NaturalAuthorityReconstruction
      (identityAuthorityObserver authorityK) where
  lift := id
  lift_forget := fun _ => rfl
  naturality := by
    intro automorphism occurrence
    exact (automorphism.forget_commutes occurrence).symm
  preservesAuthority := by
    intro automorphism occurrence
    have occurrence_eq_visible :
        automorphism.occurrenceEquiv occurrence =
          automorphism.visibleEquiv occurrence := by
      simpa [identityAuthorityObserver] using
        automorphism.forget_commutes occurrence
    calc
      authorityK (automorphism.visibleEquiv occurrence) =
          authorityK (automorphism.occurrenceEquiv occurrence) :=
        congrArg authorityK occurrence_eq_visible.symm
      _ = automorphism.authorityEquiv (authorityK occurrence) := by
        simpa [identityAuthorityObserver] using
          automorphism.authority_commutes occurrence
  readAuthority := authorityK
  preservesActualAuthority := fun _ => rfl
  recoversOccurrence := fun _ => rfl

theorem identity_observer_has_natural_authority_reconstruction
    (authorityK : Occurrence → Residual) :
    Nonempty (NaturalAuthorityReconstruction
      (identityAuthorityObserver authorityK)) :=
  ⟨identityNaturalAuthorityReconstruction authorityK⟩

end M6NaturalReconstructionIdentityControl
end Society
end ProcessGame
end SaturationMonoid
