import H0mework.Versions.X.Fock.CopyGraph.RecurrenceStep

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance historyRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

def seed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (inventoryBound runtime) (inventoryBound runtime) :=
  SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
    (oldRead (inventoryBound runtime) (sourceRead (inventoryBound runtime) index))

def recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (steps : Nat) → SourceJointClockGraph.Carrier →L[ℂ]
      FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)
  | 0 => seed runtime index
  | steps + 1 => step (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (sourceRead (inventoryBound runtime) index) (recovery runtime index steps)

theorem recovery_canonical (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    recovery runtime index steps = SourceConditionalGraphDecoder.fieldDecode
      (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (oldRead (inventoryBound runtime + steps) (sourceRead (inventoryBound runtime) index)) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [recovery, previous, step_canonical]
    rfl

theorem advance_depth (runtime : LivingRuntimeState process) (steps : Nat) :
    inventoryBound (runtime.advance steps) = inventoryBound runtime + steps := by
  rw [inventory_bound, advance_original, runtimeAt_state, inventory_bound]

theorem material_retained (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    NativeCopy.Fock.material (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) =
        NativeCopy.Fock.material (inventoryBound runtime) index :=
  SourceGraphLoss.advanced_material _ index steps

theorem read_retained (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    sourceRead (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) =
        sourceRead (inventoryBound runtime) index := by
  unfold sourceRead
  rw [material_retained]

theorem stage_recovery (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    recovery runtime index (steps + 1) =
      step (inventoryBound runtime + steps)
        (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (sourceRead (inventoryBound runtime + steps)
          (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps))
        (recovery runtime index steps) := by
  rw [read_retained]
  rfl

theorem material_history_step (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    let history := SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (steps + 1)
    let material := history.stageAt ⟨steps, Nat.lt_succ_self steps⟩
    inventoryBound material.next = inventoryBound runtime + (steps + 1) ∧
      type_of% (material.factorizes) ∧ type_of% (history.target_factorizes) ∧
      type_of% (coversAt_factorizes (runtime.advance steps) .particleWave) ∧
      type_of% (stage_recovery runtime index steps) := by
  dsimp only
  have nextDepth : inventoryBound
      ((SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (steps + 1)).stageAt
        ⟨steps, Nat.lt_succ_self steps⟩).next = inventoryBound runtime + (steps + 1) := by
    change inventoryBound (runtime.advance (steps + 1)) = _
    exact advance_depth runtime (steps + 1)
  with_reducible exact ⟨nextDepth,
    ((SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (steps + 1)).stageAt
      ⟨steps, Nat.lt_succ_self steps⟩).factorizes,
    (SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (steps + 1)).target_factorizes,
    coversAt_factorizes (runtime.advance steps) .particleWave, stage_recovery runtime index steps⟩

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
