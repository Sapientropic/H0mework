import H0mework.Physics.LowEnergy.ScalarInventory
import H0mework.Physics.SpinPair.Parameters

/-! Fixed-inventory affine one-loop diagnostics. Pairing norms are explicit:
nonabelian Tr(t^2)=1/2; normalized tY=Y/2 has native pairing norm 1/4.
This is not a threshold calculation or a GeV calibration. The physical matching
of these conventional coupling coordinates to the full BF action is separate. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Running
open Stage9C.Material.SpinPair ScalarInventory
noncomputable section

def strongInverse (time : ℝ) : ℝ :=
  (1/2) / sourceCoupling + (b0 .colorSU3 : ℝ) * time

def weakInverse (time : ℝ) : ℝ :=
  (1/2) / sourceCoupling + (b0 .weakSU2 : ℝ) * time

def normalizedChargeInverse (time : ℝ) : ℝ :=
  (1/4) / sourceCoupling + (b0 .p286HyperchargeU1 : ℝ) / 4 * time

theorem normal_forms (time : ℝ) :
    strongInverse time = 1 + 4*time ∧ weakInverse time = 1 + time/3 ∧
    normalizedChargeInverse time = 1/2 - 7*time := by
  norm_num [strongInverse, weakInverse, normalizedChargeInverse, sourceCoupling_eq,
    b0_table]
  constructor <;> first | rfl | ring

/-- Only these three specified affine trajectories are covered. This says
nothing about other source states, thresholds, or physical unification. -/
theorem no_common_crossing (time : ℝ) :
    ¬ (strongInverse time = weakInverse time ∧
      weakInverse time = normalizedChargeInverse time) := by
  rcases normal_forms time with ⟨hs, hw, hy⟩
  rw [hs, hw, hy]
  rintro ⟨h1, h2⟩
  linarith

theorem positive_on_common_interval (time : ℝ)
    (lower : -1/4 < time) (upper : time < 1/14) :
    0 < strongInverse time ∧ 0 < weakInverse time ∧
      0 < normalizedChargeInverse time := by
  rcases normal_forms time with ⟨hs, hw, hy⟩
  rw [hs, hw, hy]
  constructor
  · linarith
  constructor <;> linarith

end
end SaturationMonoid.PhysicsCore.LowEnergy.Running
