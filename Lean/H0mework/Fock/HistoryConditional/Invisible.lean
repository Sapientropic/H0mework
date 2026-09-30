import H0mework.Fock.HistoryConditional.Hidden

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem hidden_read_zero (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)))
    (steps : Nat) (early : steps ≤ length) :
    SourceGWordInverse.recover depth word (time steps (hidden depth word length)) = 0 := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply lp.ext
      funext coordinate
      change hilbert (SourceGWordInverse.recover depth word (time steps (hidden depth word length))) coordinate = 0
      rw [SourceGWordInverse.hilbert_recover]
      have floor := image_floor depth word coordinate
      dsimp only at floor
      have after : steps ≤ SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) coordinate := by omega
      rw [← Nat.sub_add_cancel after, time_hilbert_add, hidden_coordinate depth word length shorter]
      have different : hiddenIndex depth word length ≠
          SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) coordinate - steps := by
        dsimp only [hiddenIndex]
        omega
      rw [if_neg different]
    · change mass (SourceGWordInverse.recover depth word (time steps (hidden depth word length))) = 0
      rw [SourceGWordInverse.mass_recover, time_mass, hidden_mass depth word length shorter]
  · change SourceJointClockGraph.clock (SourceGWordInverse.recover depth word (time steps (hidden depth word length))) = 0
    simp only [SourceGWordInverse.clock_recover, time_clock, time_mass, hidden_mass depth word length shorter,
      hidden_clock depth word length shorter, mul_zero, add_zero, sub_zero]

theorem hidden_prefix_zero (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap length (hidden depth word length) = 0 := by
  funext index
  change SourceGWordInverse.recover depth word ((SourceJointClockGraph.action.toLinearMap ^ index.val) (hidden depth word length)) = 0
  rw [← ContinuousLinearMap.toLinearMap_pow]
  exact hidden_read_zero depth word length shorter index.val (Nat.le_of_lt_succ index.isLt)

theorem exposed_coordinate (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    hilbert (SourceGWordInverse.recover depth word (time (length + 1) (hidden depth word length))) 0 = 1 := by
  rw [SourceGWordInverse.hilbert_recover]
  have origin : SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) 0 =
      SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) := by
    simp only [SourceCopyWordAffine.execute, Nat.zero_add, mul_one, SourceInverseObservationHistory.horizon]
  rw [origin]
  have offset : hiddenIndex depth word length + (length + 1) =
      SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) := by
    dsimp only [hiddenIndex]
    omega
  rw [← offset, time_hilbert_add, hidden_coordinate depth word length shorter, if_pos rfl]

theorem hidden_next_visible (depth : Nat) (word : List (Fock.Letter depth)) (length : Nat)
    (shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) :
    SourceGeneratedActionObservationHistory.prefixEvaluator SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap length (SourceJointClockGraph.action (hidden depth word length)) ≠ 0 := by
  intro vanished
  have last := congrArg (fun values => hilbert (values (Fin.last length)) 0) vanished
  change hilbert (SourceGWordInverse.recover depth word
    ((SourceJointClockGraph.action.toLinearMap ^ length) (SourceJointClockGraph.action (hidden depth word length)))) 0 = 0 at last
  have advance : (SourceJointClockGraph.action.toLinearMap ^ length) (SourceJointClockGraph.action (hidden depth word length)) =
      time (length + 1) (hidden depth word length) := by
    rw [time, pow_succ, ← ContinuousLinearMap.toLinearMap_pow]
    rfl
  rw [advance, exposed_coordinate depth word length shorter] at last
  exact one_ne_zero last

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
