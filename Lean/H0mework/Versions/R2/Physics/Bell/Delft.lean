import H0mework.Versions.R2.Physics.Bell.Runtime


set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

namespace Delft

def alice (setting : Bool) : Axis := Axis.atAngle (if setting then Real.pi / 2 else 0)

/-- Instrument settings from the published acquisition description. -/
def bob (setting : Bool) : Axis :=
  Axis.atAngle (if setting then 97 * Real.pi / 125 else -(97 * Real.pi / 125))

def prediction (plus a b x y : Bool) : ℝ :=
  probability (alice a) (heraldAxis plus (bob b)) x y

theorem prediction_from_original_runtime (plus a b x y : Bool) (point : BasePoint) :
    runtimeProbability plus point (alice a) (bob b) x y = prediction plus a b x y :=
  runtime_probability plus point (alice a) (bob b) x y

theorem prediction_joint (plus a b : Bool) :
    (∑ x : Bool, ∑ y : Bool, prediction plus a b x y) = 1 ∧
    (∀ x y, 0 ≤ prediction plus a b x y ∧ prediction plus a b x y ≤ 1) ∧
    (∀ point x y, nextProbability plus point (alice a) (bob b) x y =
      prediction plus a b x y) := by
  exact ⟨probability_normalized _ _,
    fun x y => ⟨probability_nonnegative _ _ x y, probability_le_one _ _ x y⟩,
    fun point x y => next_probability plus point (alice a) (bob b) x y⟩

end Delft


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
