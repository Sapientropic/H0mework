import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.SocialChoice.M7.PreferenceReadout

/-!
# M7 minimal hidden-fibre control

The production theorem quantifies an arbitrary hidden carrier.  This file
keeps the two-point executable counterexample in Regression so it cannot be
mistaken for the scope of the social-choice observer law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace SocialChoice
namespace M7
namespace BooleanHiddenFibreControl

universe uVisible

def swapEquiv : Bool ≃ Bool :=
  Equiv.swap false true

theorem swap_ne (hidden : Bool) : swapEquiv hidden ≠ hidden := by
  cases hidden <;> decide

def extension : HiddenFibreExtension Bool Bool where
  authorityReadout := id
  hiddenEquiv := swapEquiv
  authorityEquiv := swapEquiv
  anchorHidden := false
  authority_commutes := fun _ => rfl
  changesAuthority := swap_ne

def attachment {Visible : Type uVisible} (visible : Visible) :=
  HiddenFibreExtension.attachment extension visible

end BooleanHiddenFibreControl
end M7
end SocialChoice
end Society
end ProcessGame
end SaturationMonoid
