import H0mework.Fock.SourceHistory.Installed

/-! The original whole-history copying primitive itself determines its action scale. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.NativeCopy

open SourceOwnedObservationHistory.Installed ArithmeticGeneration

def copy (material : Current) : Current → Current := fun state => state.joint material

def copyStep (material : Current) : Current → Current := fun state => state.parallel material

theorem copy_native_step (material state : Current) :
    copy material (nativeStep state) = copyStep material (copy material state) := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  change ((UnitHistory.next state).joint material).cardinalShadow =
    ((state.joint material).parallel material).cardinalShadow
  rw [UnitHistory.cardinalShadow_joint, UnitHistory.cardinalShadow_parallel, UnitHistory.cardinalShadow_joint]
  change (state.cardinalShadow + 1) * material.cardinalShadow =
    state.cardinalShadow * material.cardinalShadow + material.cardinalShadow
  exact Nat.succ_mul _ _

theorem unit_clock_agrees_iff (material state : Current) :
    copyStep material (copy material state) = nativeStep (copy material state) ↔
      material = CanonicalUnitArithmeticRoot.unitHistory := by
  constructor
  · intro same
    have sizes := congrArg UnitHistory.cardinalShadow same
    change ((state.joint material).parallel material).cardinalShadow =
      ((state.joint material).parallel CanonicalUnitArithmeticRoot.unitHistory).cardinalShadow at sizes
    rw [UnitHistory.cardinalShadow_parallel, UnitHistory.cardinalShadow_parallel] at sizes
    exact UnitHistory.eq_of_cardinalShadow_eq (Nat.add_left_cancel sizes)
  · rintro rfl
    rfl

end SourceOwnedObservationHistory.NativeCopy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
