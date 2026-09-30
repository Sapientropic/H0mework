import H0mework.Fock.ReceivedStep.ActionBounds

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem born_form (runtime : LivingRuntimeState process) :
    SourceConditionalInventory.born (inventoryBound runtime) = WithLp.toLp 2
      (WithLp.toLp 2 (SourceOwnedObservationHistory.SourceShift.basis (inventoryBound runtime + 2), (1 : ℂ)),
        ((inventoryBound runtime + 3 : Nat) : ℂ)) := by
  rw [SourceConditionalInventory.born_material, SourceConditionalVector.native_form]
  have actual : (runtimeAt (inventoryBound runtime + 1)).tick.next.state = inventoryBound runtime + 2 := by
    change (runtimeAt (inventoryBound runtime + 1)).state + 1 = _
    rw [runtimeAt_state]
  rw [actual]
  push_cast
  congr 2
  ring

theorem born_hilbert (runtime : LivingRuntimeState process) (position : Nat) :
    SourceCopyTimeModel.hilbert (SourceConditionalInventory.born (inventoryBound runtime)) position =
      if position = inventoryBound runtime + 2 then 1 else 0 := by
  rw [born_form]
  change SourceOwnedObservationHistory.SourceShift.basis (inventoryBound runtime + 2) position = _
  simp only [SourceOwnedObservationHistory.SourceShift.basis, lp.single_apply]
  split_ifs <;> simp_all

theorem born_mass (runtime : LivingRuntimeState process) :
    SourceCopyTimeModel.mass (SourceConditionalInventory.born (inventoryBound runtime)) = 1 := by
  rw [born_form]
  rfl

theorem born_clock (runtime : LivingRuntimeState process) :
    SourceJointClockGraph.clock (SourceConditionalInventory.born (inventoryBound runtime)) =
      ((inventoryBound runtime + 3 : Nat) : ℂ) := by
  rw [born_form]
  rfl

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
