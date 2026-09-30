import H0mework.Versions.X.Fock.PrimeFieldCalculation.FixedSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalInventory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance materialMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

theorem query_value (runtime : LivingRuntimeState process) (width : Nat)
    (actor : Fin (inventoryBound runtime + 1)) (time : Fin (width + 1)) :
    query runtime width actor time = rawField (actor.val + 1 + time.val) := by
  change FiniteRecurrence.Native.rawWindow rawField width
    ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next time = _
  rw [FiniteRecurrence.Native.rawWindow_source]
  have point : SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next =
      SourceOperationNative.statePoint process (actor.val + 1) :=
    congrArg (SourceOperationNative.statePoint process) (runtimeAt_state (actor.val + 1))
  rw [point]
  change SourcePrimeHistoryRecovery.observation
    ((nativeAction ^ time.val) (SourceOperationNative.statePoint process (actor.val + 1))) = _
  rw [source_iterate, SourceOperationNative.observer_statePoint]

theorem query_tail_birth (runtime : LivingRuntimeState process) (width : Nat)
    (actor : Fin (inventoryBound runtime + 1)) :
    query runtime (width + 1) actor (Fin.last (width + 1)) - query runtime width actor (Fin.last width) =
      SourceFactorizationAction.Fock.birth (runtimeAt (actor.val + 1 + width)).current.visit.current := by
  rw [query_value, query_value]
  change rawField (actor.val + 1 + (width + 1)) - rawField (actor.val + 1 + width) = _
  rw [show actor.val + 1 + (width + 1) = actor.val + 1 + width + 1 by omega,
    SourceGeneratedConditionalInventory.source_step, add_sub_cancel_left]

theorem query_record_prefix (runtime : LivingRuntimeState process) (width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime))
    (actor : Fin (inventoryBound runtime + 1)) (time : Fin (width + 1)) :
    query runtime width actor time =
      record runtime actor (Fin.castLE (Nat.succ_le_succ inside) time) := by
  rw [record_original, SourcePrimeCalculation.recorded_is_query]
  rfl

theorem query_actual_material (runtime : LivingRuntimeState process) (width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime))
    (actor : Fin (inventoryBound runtime + 1)) (time : Fin (width + 1)) :
    query runtime width actor time =
      rawField (material runtime (cell sourceOwner (inventoryBound runtime) actor
        (Fin.castLE (Nat.succ_le_succ inside) time))).next.state :=
  query_record_prefix runtime width inside actor time

theorem complete_record (runtime : LivingRuntimeState process) :
    query runtime (windowBound sourceOwner (inventoryBound runtime)) = record runtime := by
  funext actor time
  exact query_record_prefix runtime _ le_rfl actor time

theorem complete_cost_zero (runtime : LivingRuntimeState process) :
    costAt runtime (windowBound sourceOwner (inventoryBound runtime)) = 0 :=
  exact_inventory (inventoryBound runtime) _ (observe_injective sourceOwner (inventoryBound runtime))

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
