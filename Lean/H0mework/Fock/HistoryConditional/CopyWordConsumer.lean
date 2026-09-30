import H0mework.Fock.HistoryConditional.CopyWordRecovered
import H0mework.Fock.HistoryConditional.WordAffineEquation
import H0mework.Fock.HistoryConditional.CopyWordSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem decoded_run (bound : Nat) (actor : Fin (bound + 1)) (word : List (Option Nat)) :
    runRecovered bound word
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2 =
        some (run word (actor.val + 1)) := by
  rw [runRecovered, SourceCopyWordAffine.applyRecovered, SourceCopyNativeHistory.decoded_actor]
  simp only [Option.map_some, SourceCopyWordAffine.execute_original]

theorem material_current (bound : Nat) (actor : Fin (bound + 1)) :
    ((history runtimeSeed bound).stageAt actor).next.current.visit.current = (finiteVisit (actor.val + 1)).current := by
  change (runtimeAt (actor.val + 1)).current.visit.current = _
  exact (runtimeAt_current (actor.val + 1)).trans (finiteVisit_current (actor.val + 1)).symm

theorem recovered_word (depth bound : Nat) (word : List (Fock.Letter depth)) (actor : Fin (bound + 1)) :
    (runRecovered bound (word.map encode)
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun state => (finiteVisit state).current) =
    (SourceCopyNativeHistory.recoverMaterial bound
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun restored => Fock.actualWord depth word restored.2.next.current.visit.current) := by
  rw [decoded_run, SourceCopyNativeHistory.recovered_material]
  simp only [Option.map_some]
  apply congrArg some
  rw [material_current]
  exact (run_original depth word (actor.val + 1)).symm

theorem recovered_word_model (depth bound : Nat) (word : List (Fock.Letter depth)) (actor : Fin (bound + 1)) :
    (runRecovered bound (word.map encode)
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun state => Fock.point depth (finiteVisit state).current) =
    (SourceCopyNativeHistory.recoverMaterial bound
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun restored => SourceGeneratedActionWords.run (Fock.letterAction depth) word
          (Fock.point depth restored.2.next.current.visit.current)) := by
  rw [decoded_run, SourceCopyNativeHistory.recovered_material]
  simp only [Option.map_some]
  apply congrArg some
  rw [material_current]
  exact (model_effect depth word (actor.val + 1)).symm

end
end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
