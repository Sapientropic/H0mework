import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.RootAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBit

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open scoped Classical
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- The observed bit is acted on by the actual native step or by the cardinality
of the original material used by the copy letter. -/
def bitAction (depth : Nat) (letter : Fock.Letter depth) (bit : ZMod 2) : ZMod 2 :=
  match letter with
  | .inl _ => bit + 1
  | .inr index => bit * (scanIndex (NativeCopy.Fock.material depth index) : ZMod 2)

theorem step_observe (depth : Nat) (letter : Fock.Letter depth) (state : Current) :
    SourceWordObservedCode.observe (Fock.step depth letter state) =
      bitAction depth letter (SourceWordObservedCode.observe state) := by
  cases letter with
  | inl marker =>
      change ((state.cardinalShadow + 1 : Nat) : ZMod 2) =
        (state.cardinalShadow : ZMod 2) + 1
      push_cast
      rfl
  | inr index =>
      change (((state.joint (NativeCopy.Fock.material depth index)).cardinalShadow : Nat) : ZMod 2) =
        (state.cardinalShadow : ZMod 2) *
          ((NativeCopy.Fock.material depth index).cardinalShadow : ZMod 2)
      rw [UnitHistory.cardinalShadow_joint]
      push_cast
      rfl

def bitWord (depth : Nat) (tail : List (Fock.Letter depth)) (bit : ZMod 2) : ZMod 2 :=
  tail.foldl (fun bit letter => bitAction depth letter bit) bit

theorem word_observe (depth : Nat) (tail : List (Fock.Letter depth)) (state : Current) :
    SourceWordObservedCode.observe (Fock.actualWord depth tail state) =
      bitWord depth tail (SourceWordObservedCode.observe state) := by
  induction tail generalizing state with
  | nil => rfl
  | cons letter rest ih =>
      change SourceWordObservedCode.observe
          (Fock.actualWord depth rest (Fock.step depth letter state)) =
        bitWord depth rest (bitAction depth letter (SourceWordObservedCode.observe state))
      rw [ih, step_observe]

theorem future_bit_fibre (depth : Nat) (left right : Current) :
    (∀ tail : List (Fock.Letter depth),
      SourceWordObservedCode.observe (Fock.actualWord depth tail left) =
        SourceWordObservedCode.observe (Fock.actualWord depth tail right)) ↔
      SourceWordObservedCode.observe left = SourceWordObservedCode.observe right := by
  constructor
  · intro future
    exact future []
  · intro same tail
    rw [word_observe, word_observe, same]

theorem acted_source_future_bit_fibre (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (left right : Actors runtime) :
    (∀ tail : List (Fock.Letter (inventoryBound runtime + 1)),
      SourceWordObservedCode.observe
        (Fock.actualWord (inventoryBound runtime + 1) tail
          (SourceWordMinimalCode.executed runtime word left)) =
      SourceWordObservedCode.observe
        (Fock.actualWord (inventoryBound runtime + 1) tail
          (SourceWordMinimalCode.executed runtime word right))) ↔
      SourceWordObservedCode.sourceQuery runtime word left =
        SourceWordObservedCode.sourceQuery runtime word right := by
  exact future_bit_fibre _ _ _

end
end SourceWordFutureBit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
