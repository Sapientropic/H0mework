import H0mework.Fock.PrimeFieldJoint.ClockGraphConsumer
import Mathlib.Order.Filter.Extr

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointClockDecoder

open SourceJointClockGraph
noncomputable section

theorem residual_action (value : Carrier) : residual (action value) = 0 := by
  change action value - action (recover (action value)) = 0
  rw [recover_action, sub_self]

theorem error_decomposition (target decoder : Carrier) :
    ‖target - action decoder‖ ^ 2 = ‖residual target‖ ^ 2 + ‖action (recover target - decoder)‖ ^ 2 := by
  have paid := retained_energy (target - action decoder)
  have recovered : recover (target - action decoder) = recover target - decoder := by
    rw [map_sub, recover_action]
  have retained : residual (target - action decoder) = residual target := by
    rw [map_sub, residual_action, sub_zero]
  rw [recovered, retained] at paid
  exact paid.trans (add_comm _ _)

theorem source_minimum_cost (target : Carrier) :
    ‖target - action (recover target)‖ ^ 2 = ‖residual target‖ ^ 2 := by
  rw [error_decomposition, sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem decoder_lower (target decoder : Carrier) :
    ‖residual target‖ ^ 2 ≤ ‖target - action decoder‖ ^ 2 := by
  rw [error_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem source_minimum (target : Carrier) :
    IsMinOn (fun decoder => ‖target - action decoder‖ ^ 2) Set.univ (recover target) := by
  apply isMinOn_univ_iff.mpr
  intro decoder
  rw [source_minimum_cost]
  exact decoder_lower target decoder

theorem minimum_fibre (target decoder : Carrier) :
    ‖target - action decoder‖ ^ 2 = ‖residual target‖ ^ 2 ↔ decoder = recover target := by
  constructor
  · intro attained
    rw [error_decomposition] at attained
    have zeroNorm : ‖action (recover target - decoder)‖ ^ 2 = 0 := by linarith only [attained]
    have zero := norm_eq_zero.mp (sq_eq_zero_iff.mp zeroNorm)
    have actual := congrArg recover zero
    rw [recover_action, map_zero] at actual
    exact (sub_eq_zero.mp actual).symm
  · rintro rfl
    exact source_minimum_cost target

theorem unique_minimum (target decoder : Carrier) :
    IsMinOn (fun proposal => ‖target - action proposal‖ ^ 2) Set.univ decoder ↔ decoder = recover target := by
  constructor
  · intro minimum
    have upper := (isMinOn_univ_iff.mp minimum) (recover target)
    rw [source_minimum_cost] at upper
    exact (minimum_fibre target decoder).mp (le_antisymm upper (decoder_lower target decoder))
  · rintro rfl
    exact source_minimum target

end
end SourceJointClockDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
