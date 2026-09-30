import H0mework.Versions.X.Fock.CopyGraph.BirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation
open SourceOwnedObservationHistory SourceHistoryGrowth SourceUniformFibreVariance
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead taggedRead retainedLift oldAction taggedAction)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def priorValue (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    Space (observed (historyPMF depth) (oldRead depth read)) :=
  decoderValue (historyPMF depth) (oldRead depth read)
    (fun atom => Real.sqrt (fraction depth (depth + 1)) • value (atom, true))

theorem source_decomposition (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    pullback (historyPMF (depth + 1)) (taggedRead depth read) value =
      normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) (priorValue depth read value)) +
        value (taggedRead depth read (Fin.last (depth + 1))) • cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)) := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  change evalAt (historyPMF (depth + 1)) actor (source_positive (depth + 1) actor)
    (pullback (historyPMF (depth + 1)) (taggedRead depth read) value) =
    evalAt (historyPMF (depth + 1)) actor (source_positive (depth + 1) actor)
      (normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) (priorValue depth read value)) +
        value (taggedRead depth read (Fin.last (depth + 1))) • cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))
  rw [map_add, map_smul]
  change (pullback (historyPMF (depth + 1)) (taggedRead depth read) value) actor =
    normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) (priorValue depth read value)) actor +
      value (taggedRead depth read (Fin.last (depth + 1))) * cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)) actor
  rw [pullback_at _ _ _ actor (source_positive (depth + 1) actor), cotest_value]
  by_cases prior : actor.val < depth + 1
  · let before : Fin (depth + 1) := ⟨actor.val, prior⟩
    have same : includeActor (Nat.le_succ depth) before = actor := Fin.ext rfl
    have distinct : includeActor (Nat.le_succ depth) before ≠ Fin.last (depth + 1) := by
      intro equal
      have values := congrArg (fun point : Fin (depth + 2) => point.val) equal
      change before.val = depth + 1 at values
      have inside := before.isLt
      omega
    have tag : taggedRead depth read (includeActor (Nat.le_succ depth) before) = (oldRead depth read before, true) := by
      apply Prod.ext
      · rfl
      · change decide (before.val < depth + 1) = true
        exact decide_eq_true_eq.mpr before.isLt
    rw [← same, if_neg distinct, mul_zero, add_zero, tag, SourceGraphGrowth.normalized_prior,
      pullback_at _ _ _ before (source_positive depth before)]
    unfold priorValue
    rw [decoderValue_at _ _ _ _ (observed_supported _ _ before (source_positive depth before)),
      smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (fraction_pos depth (depth + 1))).ne', one_smul]
  · have last : actor = Fin.last (depth + 1) := Fin.ext (by have bound := actor.isLt; simp only [Fin.val_last]; omega)
    rw [last, SourceGraphGrowth.normalized_new, if_pos rfl, mul_one, zero_add]

theorem action_decomposition (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    taggedAction depth index read value = oldAction depth index read (priorValue depth read value) +
      value (taggedRead depth read (Fin.last (depth + 1))) • fresh depth index := by
  rw [SourceConditionalGraphDecoder.action_source, source_decomposition, map_add, map_smul,
    SourceGraphGrowth.tick_copy_read, ← SourceConditionalGraphDecoder.action_source]
  rfl

def freshObserved (depth : Nat) (read : Nat → Observed) :
    Space (observed (historyPMF (depth + 1)) (taggedRead depth read)) :=
  SourceConditionalCorrection.one (depth + 1) (taggedRead depth read) -
    retainedLift depth read (priorValue depth read (SourceConditionalCorrection.one (depth + 1) (taggedRead depth read)))

theorem fresh_observed_source (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    taggedAction depth index read (freshObserved depth read) = fresh depth index := by
  have one := SourceConditionalCorrection.one_at (depth + 1) (taggedRead depth read) (Fin.last (depth + 1))
  rw [pullback_at _ _ _ _ (source_positive (depth + 1) (Fin.last (depth + 1)))] at one
  have generated := action_decomposition depth index read (SourceConditionalCorrection.one (depth + 1) (taggedRead depth read))
  rw [one, one_smul] at generated
  rw [freshObserved, map_sub, SourceGraphGrowth.retained_action, generated]
  abel

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
