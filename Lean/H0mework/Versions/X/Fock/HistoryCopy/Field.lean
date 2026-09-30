import H0mework.Versions.X.Fock.HistoryCopy.Action
import H0mework.Probability.FullSource.Defect

/-! The copying source generates the correct full-field action and detects a mismatched unit action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.NativeCopy

open SourceOwnedObservationHistory.Installed

noncomputable section

theorem generated_defect_zero (material : Current) :
    FullMap.defect nativeStep (copyStep material) (copy material) = 0 :=
  (FullMap.defect_zero_iff nativeStep (copyStep material) (copy material)).mpr
    (fun state => (copy_native_step material state).symm)

theorem generated_action_square (material : Current) (value : Field nativeStep fullRead) :
    fieldAction (copyStep material) sourcePoint
        (FullMap.map nativeStep (copyStep material) (copy material) value) =
      FullMap.map nativeStep (copyStep material) (copy material) (fieldAction nativeStep fullRead value) := by
  have vanished := DFunLike.congr_fun (generated_defect_zero material) value
  change fieldAction (copyStep material) sourcePoint
      (FullMap.map nativeStep (copyStep material) (copy material) value) -
    FullMap.map nativeStep (copyStep material) (copy material) (fieldAction nativeStep fullRead value) = 0 at vanished
  exact sub_eq_zero.mp vanished

theorem unit_clock_defect_point_zero_iff (material state : Current) :
    FullMap.defect nativeStep nativeStep (copy material) (fieldPoint nativeStep fullRead state) = 0 ↔
      material = CanonicalUnitArithmeticRoot.unitHistory := by
  rw [FullMap.defect_point, sub_eq_zero, (full_fieldPoint_injective nativeStep).eq_iff, copy_native_step]
  exact eq_comm.trans (unit_clock_agrees_iff material state)

end
end SourceOwnedObservationHistory.NativeCopy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
