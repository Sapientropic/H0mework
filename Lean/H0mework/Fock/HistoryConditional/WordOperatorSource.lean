import H0mework.Fock.HistoryConditional.WordAffineEquation
import H0mework.Fock.HistoryConditional.CopyWordSource
import H0mework.Fock.HistoryPolynomial.CopyModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def action (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  Finsupp.lmapDomain ℤ ℤ (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))

theorem letter_point (depth : Nat) (letter : Fock.Letter depth) (state : Nat) :
    SourceCopyProgram.sourceLetter depth letter (SourceOperationNative.statePoint process state) =
      SourceOperationNative.statePoint process (SourceCopyNativeWord.step (SourceCopyNativeWord.encode letter) state) := by
  cases letter with
  | inl marker => exact SourceOperationNative.sourceAction_statePoint process state
  | inr index =>
      change SourceCopyProgram.action depth index (SourceOperationNative.statePoint process state) = _
      rw [SourceCopyProgram.action_point]
      exact congrArg (SourceOperationNative.statePoint process) (SourceCopyNativeKeys.copy_index depth index state)

theorem word_point (depth : Nat) (word : List (Fock.Letter depth)) (state : Nat) :
    run (SourceCopyProgram.sourceLetter depth) word (SourceOperationNative.statePoint process state) =
      SourceOperationNative.statePoint process (SourceCopyNativeWord.run (word.map SourceCopyNativeWord.encode) state) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter rest previous =>
      change run (SourceCopyProgram.sourceLetter depth) rest
        (SourceCopyProgram.sourceLetter depth letter (SourceOperationNative.statePoint process state)) = _
      rw [letter_point, previous]
      rfl

theorem action_original (depth : Nat) (word : List (Fock.Letter depth)) :
    action depth word = run (SourceCopyProgram.sourceLetter depth) word := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change Finsupp.mapDomain _ (Finsupp.single state (1 : ℤ)) =
    run (SourceCopyProgram.sourceLetter depth) word (SourceOperationNative.statePoint process state)
  rw [Finsupp.mapDomain_single, word_point, SourceCopyWordAffine.execute_original]
  rfl

theorem whole_action (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    SourceCopyProgram.whole (action depth word source) =
      run (Fock.actions depth) word (SourceCopyProgram.whole source) := by
  rw [action_original]
  exact SourceCopyProgram.whole_word depth word source

theorem complete_action (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    run (Fock.Complete.action depth) word (SourceCopyProgram.complete depth source) =
      SourceCopyProgram.complete depth (action depth word source) := by
  rw [action_original]
  exact SourceCopyProgram.complete_word depth word source

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
