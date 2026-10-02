import H0mework.Versions.R2.Physics.Actual.HistoryConfiguration
import H0mework.Versions.R2.Physics.Actual.DynamicsOnShell

/-! The original field equations settle the configuration of each later
native write. The temporal occurrences themselves continue to be generated. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.History

open Stage9C.Revision

noncomputable section

theorem nativeCurrent_add_one (index : ℕ) :
    nativeCurrent (index + 1) = .running SpinPair.initialState := by
  induction index with
  | zero => rfl
  | succ index induction =>
      change SpinPair.next (nativeCurrent (index + 1)) = _
      rw [induction]
      change SpinPair.Current.running (materialStateNext SpinPair.initialState) = _
      rw [Dynamics.accepted_materialStateNext]

theorem configuration_add_seven_eq_firstWrite (index : ℕ) :
    configuration (index + 7) = configuration 7 := by
  rw [configuration_add_seven, nativeCurrent_add_one]
  rfl

theorem configuration_eventually_firstWrite :
    ∀ᶠ index in Filter.atTop, configuration index = configuration 7 := by
  filter_upwards [Filter.eventually_ge_atTop 7] with index later
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  simpa only [Nat.add_comm] using configuration_add_seven_eq_firstWrite offset

end
end SaturationMonoid.PhysicsCore.Stage9CU.History
