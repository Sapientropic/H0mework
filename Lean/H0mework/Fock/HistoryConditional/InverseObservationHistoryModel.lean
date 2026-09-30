import H0mework.Fock.HistoryConditional.InverseObservationHistoryRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceGeneratedActionWords
noncomputable section

theorem kernel_zero (depth : Nat) (word : List (Fock.Letter depth)) :
    LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap) = ⊥ := by
  apply bot_unique
  intro value invisible
  change value = 0
  apply window_injective depth word
  have zero : window depth word value = 0 := by
    funext index
    exact (SourceGeneratedActionObservationHistory.mem_kernel_iff SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap value).mp invisible index.val
  exact zero.trans (map_zero _).symm

def modelWindow (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceGeneratedActionObservationHistory.Model SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap →ₗ[ℂ]
        SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier
          (horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :=
  (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap SourceJointClockGraph.action.toLinearMap
    (SourceGWordInverse.recover depth word).toLinearMap)).liftQ (window depth word) (by
      intro value invisible
      change window depth word value = 0
      funext index
      exact (SourceGeneratedActionObservationHistory.mem_kernel_iff SourceJointClockGraph.action.toLinearMap
        (SourceGWordInverse.recover depth word).toLinearMap value).mp invisible index.val)

theorem modelWindow_projection (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    modelWindow depth word (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap value) = window depth word value := rfl

def restore (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceGeneratedActionObservationHistory.Model SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
    (SourceCompiledWordOperator.slope_positive _)).comp (modelWindow depth word)

theorem restore_projection (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    restore depth word (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap value) = value :=
  read_window depth word value

theorem projection_restore (depth : Nat) (word : List (Fock.Letter depth))
    (model : SourceGeneratedActionObservationHistory.Model SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap) :
    SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap (restore depth word model) = model := by
  obtain ⟨value, rfl⟩ := (SourceGeneratedActionObservationHistory.actionRow SourceJointClockGraph.action.toLinearMap
    (SourceGWordInverse.recover depth word).toLinearMap).restriction_surjective model
  dsimp only [SourceGeneratedActionObservationHistory.actionRow]
  rw [restore_projection]

theorem model_action_restore (depth : Nat) (word : List (Fock.Letter depth))
    (model : SourceGeneratedActionObservationHistory.Model SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap) :
    restore depth word (SourceGeneratedActionObservationHistory.modelAction SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap model) =
      SourceJointClockGraph.action (restore depth word model) := by
  obtain ⟨value, rfl⟩ := (SourceGeneratedActionObservationHistory.actionRow SourceJointClockGraph.action.toLinearMap
    (SourceGWordInverse.recover depth word).toLinearMap).restriction_surjective model
  dsimp only [SourceGeneratedActionObservationHistory.actionRow]
  rw [SourceGeneratedActionObservationHistory.modelAction_source, restore_projection, restore_projection]
  rfl

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
