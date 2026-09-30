import H0mework.Realization.HilbertTransfer.Retained

/-! The one shared finite chain fold retains every generated isometry's complete residual fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer.Chain

noncomputable section

universe u

variable {H : Nat → Type u}
variable [∀ depth, NormedAddCommGroup (H depth)] [∀ depth, InnerProductSpace ℂ (H depth)]
variable [∀ depth, CompleteSpace (H depth)]
variable (pullback : ∀ depth, H (depth + 1) →ₗᵢ[ℂ] H depth)

def Inventory : Nat → Type u
  | 0 => PUnit
  | depth + 1 => Inventory depth × ResidualSpace (pullback depth)

instance inventoryAddCommGroup (depth : Nat) : AddCommGroup (Inventory pullback depth) := by
  induction depth with
  | zero => exact inferInstanceAs (AddCommGroup PUnit)
  | succ depth previous =>
      letI := previous
      exact inferInstanceAs (AddCommGroup (Inventory pullback depth ×
        ResidualSpace (pullback depth)))

instance inventoryModule (depth : Nat) : Module ℂ (Inventory pullback depth) := by
  induction depth with
  | zero => exact inferInstanceAs (Module ℂ PUnit)
  | succ depth previous =>
      letI := previous
      exact inferInstanceAs (Module ℂ (Inventory pullback depth ×
        ResidualSpace (pullback depth)))

def retainedHistory : (depth : Nat) → H 0 ≃ₗ[ℂ]
    H depth × Inventory pullback depth
  | 0 => by
      change H 0 ≃ₗ[ℂ] H 0 × PUnit
      exact LinearEquiv.prodUnique.symm
  | depth + 1 =>
      (retainedHistory depth).trans
        (((retainedUpdate (pullback depth)).prodCongr
          (LinearEquiv.refl ℂ (Inventory pullback depth))).trans
        ((LinearEquiv.prodAssoc ℂ _ _ _).trans
          ((LinearEquiv.refl ℂ _).prodCongr (LinearEquiv.prodComm ℂ _ _))))

def inventoryEnergy : (depth : Nat) → Inventory pullback depth → ℝ
  | 0, _ => 0
  | depth + 1, inventory => inventoryEnergy depth inventory.1 + ‖inventory.2‖ ^ 2

theorem retainedHistory_energy (depth : Nat) (value : H 0) :
    ‖value‖ ^ 2 = ‖(retainedHistory pullback depth value).1‖ ^ 2 +
      inventoryEnergy pullback depth (retainedHistory pullback depth value).2 := by
  induction depth with
  | zero =>
      change ‖value‖ ^ 2 = ‖value‖ ^ 2 + 0
      exact (add_zero _).symm
  | succ depth previous =>
      have step := retainedUpdate_energy (pullback depth)
        (retainedHistory pullback depth value).1
      change ‖value‖ ^ 2 =
        ‖(retainedUpdate (pullback depth) (retainedHistory pullback depth value).1).1‖ ^ 2 +
        (inventoryEnergy pullback depth (retainedHistory pullback depth value).2 +
          ‖(retainedUpdate (pullback depth) (retainedHistory pullback depth value).1).2‖ ^ 2)
      linarith only [previous, step]


end
end IsometricRetainedTransfer.Chain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
