import H0mework.Versions.X.Fock.HistoryConditional.InverseObservationHistoryAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

def window (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceJointClockGraph.Carrier →ₗ[ℂ]
      SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier
        (horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :=
  SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
    (SourceGWordInverse.recover depth word).toLinearMap
    (horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))

theorem coordinate (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) (index : Nat) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    hilbert (window depth word value (sampleIndex program index)) (index / program.1) = hilbert value index := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  change hilbert (SourceGWordInverse.recover depth word
    ((SourceJointClockGraph.action.toLinearMap ^ delay program index) value)) (index / program.1) = _
  rw [SourceGWordInverse.hilbert_recover, execute_delay program (SourceCompiledWordOperator.slope_positive _)]
  exact hilbert_power _ value index

theorem first_sample (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    window depth word value 0 = SourceGWordInverse.recover depth word value := rfl

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
