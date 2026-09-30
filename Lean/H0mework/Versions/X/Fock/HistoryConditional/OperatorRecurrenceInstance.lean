import H0mework.Versions.X.Fock.HistoryConditional.OperatorRecurrenceSource
import H0mework.Realization.Operators.ObservedKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

def lag (depth : Nat) (word : List (Fock.Letter depth)) :
    Fin (SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) + 1) :=
  ⟨(SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2, by
    have positive := SourceCompiledWordOperator.slope_positive (word.map SourceCopyNativeWord.encode)
    dsimp only [SourceInverseObservationHistory.horizon]
    omega⟩

def coefficients (depth : Nat) (word : List (Fock.Letter depth)) :
    Fin (SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) + 1) →
      SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  fun index => if index = lag depth word then SourceJointClockGraph.action.toLinearMap else 0

theorem source_law (depth : Nat) (word : List (Fock.Letter depth)) :
    let bound := SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
    (SourceGWordInverse.recover depth word).toLinearMap.comp (SourceJointClockGraph.action.toLinearMap ^ (bound + 1)) =
      ∑ index : Fin (bound + 1), (coefficients depth word index).comp
        (SourceGeneratedActionObservationHistory.stageEvaluator SourceJointClockGraph.action.toLinearMap
          (SourceGWordInverse.recover depth word).toLinearMap index.val) := by
  dsimp only
  apply LinearMap.ext
  intro value
  rw [LinearMap.sum_apply]
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  have length : SourceInverseObservationHistory.horizon program + 1 = program.1 + program.2 := by
    have positive : 0 < program.1 := SourceCompiledWordOperator.slope_positive _
    dsimp only [SourceInverseObservationHistory.horizon]
    omega
  trans SourceJointClockGraph.action (SourceGWordInverse.recover depth word (time program.2 value))
  · change SourceGWordInverse.recover depth word
      ((SourceJointClockGraph.action.toLinearMap ^ (SourceInverseObservationHistory.horizon program + 1)) value) = _
    rw [length, ← ContinuousLinearMap.toLinearMap_pow]
    exact feedback depth word value
  · symm
    rw [Finset.sum_eq_single (lag depth word)]
    · simp only [coefficients, LinearMap.comp_apply,
        SourceGeneratedActionObservationHistory.stageEvaluator]
      rw [← ContinuousLinearMap.toLinearMap_pow]
      rfl
    · intro index _ different
      simp only [coefficients, if_neg different, LinearMap.zero_comp, LinearMap.zero_apply]
    · intro absent
      exact (absent (Finset.mem_univ _)).elim

theorem prefix_fibre (depth : Nat) (word : List (Fock.Letter depth)) (left right : SourceJointClockGraph.Carrier) :
    SourceInverseObservationHistory.window depth word left = SourceInverseObservationHistory.window depth word right ↔
      SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceGWordInverse.recover depth word).toLinearMap left =
      SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceGWordInverse.recover depth word).toLinearMap right :=
  SourceGeneratedActionObservationHistory.OperatorRecurrence.prefix_fibre_iff_model SourceJointClockGraph.action.toLinearMap
    (SourceGWordInverse.recover depth word).toLinearMap _ (coefficients depth word) (source_law depth word) left right

def next (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier
      (SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) →ₗ[ℂ]
    SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier
      (SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :=
  SourceGeneratedActionObservationHistory.OperatorRecurrence.advance _ (coefficients depth word)

theorem next_source (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    next depth word (SourceInverseObservationHistory.window depth word value) =
      SourceInverseObservationHistory.window depth word (SourceJointClockGraph.action value) :=
  LinearMap.congr_fun (SourceGeneratedActionObservationHistory.OperatorRecurrence.advance_source
    SourceJointClockGraph.action.toLinearMap (SourceGWordInverse.recover depth word).toLinearMap _
    (coefficients depth word) (source_law depth word)) value

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
