import H0mework.Fock.HistoryConditional.NativeInverseRows
import H0mework.Fock.HistoryConditional.CopyWordConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords
open SourceOwnedObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem actual_index (depth bound : Nat) (word : List (Fock.Letter depth)) (actor : Fin (bound + 1)) :
    NativeWindow.bound (Fock.actualWord depth word ((history runtimeSeed bound).stageAt actor).next.current.visit.current) =
      SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (actor.val + 1) := by
  rw [SourceCopyNativeWord.material_current, SourceCopyNativeWord.run_original]
  change (finiteVisit (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode) (actor.val + 1))).current.cardinalShadow - 1 = _
  rw [finiteVisit_current, ArithmeticGeneration.UnitHistory.cardinalShadow_generate, SourceCopyWordAffine.execute_original]
  rfl

theorem material_original (depth bound : Nat) (word : List (Fock.Letter depth)) (actor : Fin (bound + 1)) :
    SourceCopyNativeHistory.recoverMaterial bound
      (row bound (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (NativeWindow.bound (Fock.actualWord depth word ((history runtimeSeed bound).stageAt actor).next.current.visit.current))) =
      some ⟨actor, (history runtimeSeed bound).stageAt actor⟩ := by
  rw [actual_index]
  exact material_execute bound _ (SourceCompiledWordOperator.slope_positive _) actor

theorem material_next (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (actor : SourceConditionalModel.Actors runtime) :
    (SourceCopyNativeHistory.recoverMaterial (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)
      (row (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (NativeWindow.bound (Fock.actualWord depth word
          ((history runtimeSeed (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)).stageAt actor).next.current.visit.current)))).map
      (fun recovered => SourceCopyNativeSharedUpdate.modelStep runtime.tick.next (SourceConditionalModel.nextRead runtime recovered.1)) =
        some (SourceConditionalModel.nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) := by
  rw [material_original]
  exact congrArg some (SourceActualImageStep.model_step_source runtime actor)

end
end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
