import H0mework.Realization.HilbertTransfer.Chain

/-! Terminal estimation consumes the existing complete retained-history equivalence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer.Chain

noncomputable section

universe u

variable {H : Nat → Type u}
variable [∀ depth, NormedAddCommGroup (H depth)] [∀ depth, InnerProductSpace ℂ (H depth)]
variable [∀ depth, CompleteSpace (H depth)]
variable (pullback : ∀ depth, H (depth + 1) →ₗᵢ[ℂ] H depth)

omit [∀ depth, CompleteSpace (H depth)] in
theorem inventoryEnergy_zero (depth : Nat) : inventoryEnergy pullback depth 0 = 0 := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      change inventoryEnergy pullback depth 0 + ‖(0 : ResidualSpace (pullback depth))‖ ^ 2 = 0
      rw [previous, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

omit [∀ depth, CompleteSpace (H depth)] in
theorem inventoryEnergy_nonnegative (depth : Nat) (inventory : Inventory pullback depth) :
    0 ≤ inventoryEnergy pullback depth inventory := by
  induction depth with
  | zero => exact le_refl _
  | succ depth previous =>
      exact add_nonneg (previous inventory.1) (sq_nonneg ‖inventory.2‖)

theorem terminal_error (depth : Nat) (value : H 0) (decoder : H depth) :
    ‖value - (retainedHistory pullback depth).symm (decoder, 0)‖ ^ 2 =
      inventoryEnergy pullback depth (retainedHistory pullback depth value).2 +
        ‖(retainedHistory pullback depth value).1 - decoder‖ ^ 2 := by
  have energy := retainedHistory_energy pullback depth
    (value - (retainedHistory pullback depth).symm (decoder, 0))
  simpa only [map_sub, LinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero, add_comm] using energy

theorem terminal_attains (depth : Nat) (value : H 0) :
    ‖value - (retainedHistory pullback depth).symm ((retainedHistory pullback depth value).1, 0)‖ ^ 2 =
      inventoryEnergy pullback depth (retainedHistory pullback depth value).2 := by
  rw [terminal_error, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem terminal_lower_bound (depth : Nat) (value : H 0) (decoder : H depth) :
    inventoryEnergy pullback depth (retainedHistory pullback depth value).2 ≤
      ‖value - (retainedHistory pullback depth).symm (decoder, 0)‖ ^ 2 := by
  rw [terminal_error]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem source_lift_succ (depth : Nat) (decoder : H (depth + 1)) :
    (retainedHistory pullback (depth + 1)).symm (decoder, 0) =
      (retainedHistory pullback depth).symm (pullback depth decoder, 0) := by
  change (retainedHistory pullback depth).symm (reconstruct (pullback depth) (decoder, 0), 0) = _
  have lifted : reconstruct (pullback depth) (decoder, 0) = pullback depth decoder := add_zero _
  rw [lifted]

theorem floor_succ (depth : Nat) (value : H 0) :
    inventoryEnergy pullback (depth + 1) (retainedHistory pullback (depth + 1) value).2 =
      inventoryEnergy pullback depth (retainedHistory pullback depth value).2 +
        ‖residual (pullback depth) (retainedHistory pullback depth value).1‖ ^ 2 := rfl

theorem floor_monotone (value : H 0) :
    Monotone (fun depth => inventoryEnergy pullback depth (retainedHistory pullback depth value).2) := by
  apply monotone_nat_of_le_succ
  intro depth
  rw [floor_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end IsometricRetainedTransfer.Chain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
