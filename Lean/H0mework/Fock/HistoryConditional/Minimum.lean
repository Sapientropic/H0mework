import H0mework.Fock.HistoryConditional.Invisible

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords
noncomputable section

theorem no_short_update (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    ¬ ∃ advance : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier length →
        SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier length,
      ∀ value : SourceJointClockGraph.Carrier,
        advance (SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
          (SourceGWordInverse.recover depth word).toLinearMap length value) =
        SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
          (SourceGWordInverse.recover depth word).toLinearMap length (SourceJointClockGraph.action value) := by
  rintro ⟨advance, sourceLaw⟩
  have origin := sourceLaw 0
  simp only [map_zero] at origin
  have actual := sourceLaw (hidden depth word length)
  rw [hidden_prefix_zero depth word length shorter, origin] at actual
  exact hidden_next_visible depth word length shorter actual.symm

theorem least_window (depth : Nat) (word : List (Fock.Letter depth)) :
    IsLeast {length : Nat | ∃ advance : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier length →
        SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier length,
      ∀ value : SourceJointClockGraph.Carrier,
        advance (SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
          (SourceGWordInverse.recover depth word).toLinearMap length value) =
        SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
          (SourceGWordInverse.recover depth word).toLinearMap length (SourceJointClockGraph.action value)}
      (SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) := by
  constructor
  · exact ⟨next depth word, next_source depth word⟩
  · intro length admitted
    exact le_of_not_gt (fun shorter => no_short_update depth word length shorter admitted)

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
