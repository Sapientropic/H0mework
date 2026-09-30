import H0mework.Versions.X.Fock.CopyGraph.LossNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceOwnedObservationHistory SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance traceLossMeasurable : MeasurableSpace ParentCarrier := ⊤

def advancedIndex (depth : Nat) (index : Index depth) : (steps : Nat) → Index (depth + steps)
  | 0 => index
  | steps + 1 => FamilyModel.Fock.oldIndex (depth + steps) (advancedIndex depth index steps)

theorem advanced_material (depth : Nat) (index : Index depth) (steps : Nat) :
    NativeCopy.Fock.material (depth + steps) (advancedIndex depth index steps) = NativeCopy.Fock.material depth index := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    exact (SourceGraphGrowth.old_material (depth + steps) (advancedIndex depth index steps)).trans previous

def stepRank (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (step : Nat) : Nat :=
  Module.finrank ℂ (SourceGraphGrowth.forgettingLoss (inventoryBound runtime + step)
    (advancedIndex (inventoryBound runtime) index step) (SourceGraphGrowth.sourceRead (inventoryBound runtime) index)).range

theorem step_rank_increment (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (step : Nat) :
    (stepRank runtime index step : ℝ) = SourceCopyInventory.increment (NativeCopy.Fock.material (inventoryBound runtime) index)
      (runtime.advance step).state := by
  have original := native_rank_increment (inventoryBound runtime + step) (advancedIndex (inventoryBound runtime) index step)
  unfold SourceGraphGrowth.sourceRead at original
  rw [advanced_material] at original
  have clock : (runtime.advance step).state = inventoryBound runtime + step := by
    rw [advance_original, runtimeAt_state, inventory_bound]
  rw [clock]
  exact original

theorem normal_rank_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) index
    SourceCopyInventory.inventoryCost material (normal runtime).targetRuntime.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ step ∈ Finset.range ((frontier runtime).stageCount + 1), (stepRank runtime index step : ℝ) := by
  have original := SourceCopyInventory.normal_copy_cost runtime index
  simp_rw [step_rank_increment]
  exact original

theorem generated_next_rank_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) index
    SourceCopyInventory.inventoryCost material (normal runtime).targetRuntime.tick.next.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ step ∈ Finset.range ((frontier runtime).stageCount + 2), (stepRank runtime index step : ℝ) := by
  have original := SourceCopyInventory.generated_next_copy_cost runtime index
  simp_rw [step_rank_increment]
  exact original

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
