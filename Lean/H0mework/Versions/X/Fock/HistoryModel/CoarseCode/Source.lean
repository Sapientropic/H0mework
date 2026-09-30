import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertRecovery
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.RootAction
import H0mework.Probability.Source.ConditionalCoarsening

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedActionWords.Fock
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

abbrev FullField (depth : Nat) := Field nativeStep (rawWords (depth + 1))

local instance fieldUniformSpace (depth : Nat) : UniformSpace (FullField depth) :=
  fieldUniform nativeStep (rawWords (depth + 1))
local instance fieldMeasurable (depth : Nat) : MeasurableSpace (FullField depth) :=
  fieldBorel nativeStep (rawWords (depth + 1))
local instance fieldBorelSpace (depth : Nat) : BorelSpace (FullField depth) := ⟨rfl⟩
local instance fieldT2 (depth : Nat) : T2Space (FullField depth) :=
  Actor.conditionalFieldT2 (depth + 1)

def actualActor (depth : Nat) (atom : FullField depth) : Fin (depth + 1) :=
  if h : ∃ actor : Fin (depth + 1), Actor.nextRead (depth + 1) depth actor = atom then
    Classical.choose h
  else 0

theorem actualActor_left (depth : Nat) (actor : Fin (depth + 1)) :
    actualActor depth (Actor.nextRead (depth + 1) depth actor) = actor := by
  unfold actualActor
  split_ifs with h
  · exact next_read_injective (depth + 1) depth (Classical.choose_spec h)
  · exact False.elim (h ⟨actor, rfl⟩)

def fieldCode (depth : Nat) (word : List (Letter (depth + 1)))
    (atom : FullField depth) : ZMod 2 :=
  if ∃ actor : Fin (depth + 1), Actor.nextRead (depth + 1) depth actor = atom then
    SourceWordObservedCode.observe
      (actualWord (depth + 1) word
        (runtimePayload (actualActor depth atom).val).nativeWrite.target)
  else 0

theorem outside_actual_support_zero (depth : Nat) (word : List (Letter (depth + 1)))
    (atom : FullField depth)
    (outside : ¬∃ actor : Fin (depth + 1), Actor.nextRead (depth + 1) depth actor = atom) :
    fieldCode depth word atom = 0 := by
  simp [fieldCode, outside]

theorem actual_square (depth : Nat) (word : List (Letter (depth + 1)))
    (actor : Fin (depth + 1)) :
    fieldCode depth word (Actor.nextRead (depth + 1) depth actor) =
      SourceWordObservedCode.readAt depth word actor.val := by
  unfold fieldCode
  split_ifs with h
  · have sameIndex : (actualActor depth (Actor.nextRead (depth + 1) depth actor)).val = actor.val :=
      congrArg Fin.val (actualActor_left depth actor)
    exact (congrArg (fun index : Nat => SourceWordObservedCode.observe
      (actualWord (depth + 1) word (runtimePayload index).nativeWrite.target)) sameIndex).trans rfl
  · exact False.elim (h ⟨actor, rfl⟩)

theorem native_square (depth : Nat) (actor : Fin (depth + 1)) :
    fieldCode depth [] (Actor.nextRead (depth + 1) depth actor) =
      SourceWordNativeAlignment.nativeObservation (runtimePayload actor.val) := by
  rw [actual_square]
  exact (SourceWordNativeAlignment.payload_native_observe depth actor.val).symm

theorem observed_square (depth : Nat) (word : List (Letter (depth + 1))) :
    observed (observed (historyPMF depth) (Actor.nextRead (depth + 1) depth))
        (fieldCode depth word) =
      observed (historyPMF depth)
        (fun actor => SourceWordObservedCode.readAt depth word actor.val) := by
  rw [observed, observed, PMF.map_comp]
  congr 1
  funext actor
  exact actual_square depth word actor

theorem mixture_full (depth : Nat) (word : List (Letter (depth + 1)))
    (key : ZMod 2)
    (supported : key ∈ (observed
      (observed (historyPMF depth) (Actor.nextRead (depth + 1) depth))
      (fieldCode depth word)).support) :
    ∃ coarseSupported : key ∈ (observed (historyPMF depth)
        (fun actor => SourceWordObservedCode.readAt depth word actor.val)).support,
      Coarsening.mixture (historyPMF depth) (Actor.nextRead (depth + 1) depth)
        (fieldCode depth word) key supported =
        conditional (historyPMF depth)
          (fun actor => SourceWordObservedCode.readAt depth word actor.val)
          key coarseSupported := by
  have square : (fieldCode depth word) ∘ (Actor.nextRead (depth + 1) depth) =
      (fun actor => SourceWordObservedCode.readAt depth word actor.val) := by
    funext actor
    exact actual_square depth word actor
  simpa only [square] using (Coarsening.mixture_is_conditional
    (historyPMF depth) (Actor.nextRead (depth + 1) depth)
    (fieldCode depth word) key supported)


end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
