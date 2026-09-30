import H0mework.Versions.X.Arithmetic.UnitArithmetic.Root

/-! The full past window is recovered as native unit-history prefixes, up to the actual next write. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.NativeWindow

open CanonicalUnitArithmeticRoot ArithmeticGeneration

def bound (current : Current) : Nat := current.cardinalShadow - 1

def point (current : Current) (index : Fin (bound current + 1)) : Current :=
  next^[index.val] initialCurrent

def imagePoint (current : Current) (index : Fin (bound current + 1)) : Current :=
  next (point current index)

private theorem iterate_shadow (state : Current) (depth : Nat) :
    (next^[depth] state).cardinalShadow = state.cardinalShadow + depth := by
  induction depth with
  | zero => exact (Nat.add_zero _).symm
  | succ depth previous =>
      rw [Function.iterate_succ_apply']
      change (next^[depth] state).cardinalShadow + 1 = _
      rw [previous, Nat.add_assoc]

theorem last_source (current : Current) (active : 1 ≤ current.cardinalShadow) :
    next^[bound current] initialCurrent = current := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [iterate_shadow]
  change 1 + (current.cardinalShadow - 1) = current.cardinalShadow
  omega

theorem point_prefix (current : Current) (active : 1 ≤ current.cardinalShadow)
    (index : Fin (bound current + 1)) :
    next^[bound current - index.val] (point current index) = current := by
  have inBound : index.val ≤ bound current := Nat.le_of_lt_succ index.isLt
  change next^[bound current - index.val] (next^[index.val] initialCurrent) = current
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel inBound]
  exact last_source current active

theorem image_prefix (current : Current) (active : 1 ≤ current.cardinalShadow)
    (index : Fin (bound current + 1)) :
    next^[bound current - index.val] (imagePoint current index) = next current := by
  have commutes := (Function.iterate_succ_apply next (bound current - index.val)
    (point current index)).symm.trans
      (Function.iterate_succ_apply' next (bound current - index.val) (point current index))
  exact commutes.trans (congrArg next (point_prefix current active index))

theorem last_image (current : Current) (active : 1 ≤ current.cardinalShadow) :
    next^[bound current] (next initialCurrent) = next current := by
  have commutes := (Function.iterate_succ_apply next (bound current) initialCurrent).symm.trans
    (Function.iterate_succ_apply' next (bound current) initialCurrent)
  exact commutes.trans (congrArg next (last_source current active))

theorem native_last_image {current : Current} (active : 1 ≤ current.cardinalShadow)
    (write : NativeWriteAt current) :
    next^[bound current] (next initialCurrent) = write.target :=
  (last_image current active).trans write.target_eq.symm

theorem native_image_prefix {current : Current} (active : 1 ≤ current.cardinalShadow)
    (write : NativeWriteAt current) (index : Fin (bound current + 1)) :
    next^[bound current - index.val] (imagePoint current index) = write.target :=
  (image_prefix current active index).trans write.target_eq.symm

end SourceOwnedObservationHistory.NativeWindow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
