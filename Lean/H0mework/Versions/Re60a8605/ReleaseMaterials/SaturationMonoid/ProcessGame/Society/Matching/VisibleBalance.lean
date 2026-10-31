import Mathlib.Logic.Function.Basic

/-!
# Visible matching balance

Matching can positively balance two visible readouts without identifying the
actual occurrence or its authority.  The interface is scale-free: visible
images and balance values are arbitrary types, and balance is an equality of
two computations on the same visible image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Matching

universe uVisible uBalance

/-- Two sides of a matching computation defined only on visible images. -/
structure VisibleBalanceReadout
    (Visible : Type uVisible)
    (Balance : Type uBalance) where
  leftBalance : Visible → Balance
  rightBalance : Visible → Balance

namespace VisibleBalanceReadout

variable {Visible : Type uVisible}
variable {Balance : Type uBalance}

/-- Positive balance at one visible image.  It carries no claim about hidden
occurrence identity, lineage, or authority. -/
structure BalancedAt
    (readout : VisibleBalanceReadout Visible Balance)
    (visible : Visible) : Prop where
  balance_eq : readout.leftBalance visible = readout.rightBalance visible

/-- The visible images on which the matching computation balances. -/
def BalancedImage
    (readout : VisibleBalanceReadout Visible Balance) : Type uVisible :=
  { visible : Visible // readout.BalancedAt visible }

theorem balancedImage_has_positive_witness
    (readout : VisibleBalanceReadout Visible Balance)
    (visible : Visible)
    (balanced : readout.leftBalance visible = readout.rightBalance visible) :
    Nonempty readout.BalancedImage :=
  ⟨⟨visible, ⟨balanced⟩⟩⟩

end VisibleBalanceReadout

end Matching
end Society
end ProcessGame
end SaturationMonoid
