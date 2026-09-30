import H0mework.Fock.HistoryConditional.ActualImageMaterial
import H0mework.Probability.Information.InventoryInformation
import H0mework.Probability.Information.Capacity

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery SourceGeneratedAtomicObservation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def coordinateRead (address : Nat) : SourceJointClockGraph.Carrier →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : Nat => ℂ) 2 address).comp
    (SourceMassCompletion.firstRead.comp SourceJointClockGraph.joint)

theorem coordinate_actual (bound : Nat) (actor index : Fin (bound + 1)) :
    coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index) = if index = actor then 1 else 0 := by
  change SourceCopyTimeModel.hilbert
    (SourceCopyNativeModelStep.sourceValue ((history runtimeSeed bound).stageAt index).next) (actor.val + 1) = _
  rw [SourceCopyPhaseRecovery.native_hilbert]
  change (if actor.val + 1 = (runtimeAt (index.val + 1)).state then (1 : ℂ) else 0) = _
  rw [runtimeAt_state]
  by_cases same : index = actor
  · subst index
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun equal => same (Fin.ext (Nat.add_right_cancel equal).symm)), if_neg same]

theorem coordinate_cotest (bound : Nat) (actor : Fin (bound + 1)) :
    taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)) =
      cotest (historyPMF bound) actor := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  rw [taskValue_at _ _ _ (SourceUniformFibreVariance.source_positive bound index), coordinate_actual,
    SourceHistoryGrowth.cotest_value]

theorem unit_original_coordinate (bound : Nat) (actor : Fin (bound + 1)) :
    taskValue (historyPMF bound) (fun index => (SourceConditionalInventory.unitTask bound actor index : ℂ)) =
      (Real.sqrt (bound + 1 : ℝ) : ℂ) • taskValue (historyPMF bound)
        (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)) := by
  rw [coordinate_cotest]
  exact SourceConditionalInventory.unit_is_original_cotest bound actor

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
