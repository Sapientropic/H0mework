import H0mework.Fock.HistoryConditional.CopyWordConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem original_reader (depth bound : Nat) (word : List (Fock.Letter depth)) (actor : Fin (bound + 1))
    (index : FamilyModel.Fock.Index depth) :
    (runRecovered bound (word.map encode)
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun state => sourceStateAt
          (NativeCopy.copy (NativeCopy.Fock.material depth index) (finiteVisit state).current)) =
    (SourceCopyNativeHistory.recoverMaterial bound
      (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound (SourceCopyNativeHistory.read bound actor.val)).2).map
        (fun restored => FamilyModel.Fock.readout depth
          (Fock.restrict depth (SourceGeneratedActionWords.run (Fock.letterAction depth) word
            (Fock.point depth restored.2.next.current.visit.current))) index) := by
  rw [decoded_run, SourceCopyNativeHistory.recovered_material]
  simp only [Option.map_some]
  apply congrArg some
  rw [material_current]
  have original := Fock.read_word depth word (finiteVisit (actor.val + 1)).current index
  rw [run_original] at original
  exact original.symm

end
end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
