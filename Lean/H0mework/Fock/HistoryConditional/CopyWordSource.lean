import H0mework.Fock.HistoryConditional.CopyWordNative
import H0mework.Fock.HistoryConditional.CopyHistoryMaterial
import H0mework.Fock.HistoryModel.CompletionConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

def encode {depth : Nat} : Fock.Letter depth → Option Nat
  | .inl _ => none
  | .inr index => some index.val

noncomputable section

theorem step_original (depth : Nat) (letter : Fock.Letter depth) (state : Nat) :
    Fock.step depth letter (finiteVisit state).current = (finiteVisit (step (encode letter) state)).current := by
  cases letter with
  | inl marker =>
      change nativeStep (finiteVisit state).current = (finiteVisit (state + 1)).current
      rw [finiteVisit_current, finiteVisit_current]
      rfl
  | inr index =>
      change NativeCopy.copy (NativeCopy.Fock.material depth index) (finiteVisit state).current =
        (finiteVisit ((state + 1) * (index.val + 1) - 1)).current
      rw [← SourceCopyNativeKeys.copy_index depth index state]
      exact (SourceCopyProgram.actual_copy_state depth index state).symm

theorem run_original (depth : Nat) (word : List (Fock.Letter depth)) (state : Nat) :
    Fock.actualWord depth word (finiteVisit state).current = (finiteVisit (run (word.map encode) state)).current := by
  induction word generalizing state with
  | nil => rfl
  | cons letter rest previous =>
      change Fock.actualWord depth rest (Fock.step depth letter (finiteVisit state).current) =
        (finiteVisit (run (rest.map encode) (step (encode letter) state))).current
      rw [step_original, previous]

theorem model_effect (depth : Nat) (word : List (Fock.Letter depth)) (state : Nat) :
    SourceGeneratedActionWords.run (Fock.letterAction depth) word (Fock.point depth (finiteVisit state).current) =
      Fock.point depth (finiteVisit (run (word.map encode) state)).current := by
  exact (Fock.word_point depth word (finiteVisit state).current).trans
    (congrArg (Fock.point depth) (run_original depth word state))

end
end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
