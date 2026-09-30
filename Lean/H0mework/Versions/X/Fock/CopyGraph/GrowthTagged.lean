import H0mework.Versions.X.Fock.CopyGraph.GrowthSamples

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance SourceHistoryGrowth
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def oldRead (depth : Nat) (read : Nat → Observed) (actor : Fin (depth + 1)) : Observed := read actor.val

def newRead (depth : Nat) (read : Nat → Observed) (actor : Fin (depth + 2)) : Observed := read actor.val

def taggedRead (depth : Nat) (read : Nat → Observed) (actor : Fin (depth + 2)) : Observed × Bool :=
  (newRead depth read actor, priorTag depth (depth + 1) actor)

def retainedLift (depth : Nat) (read : Nat → Observed) :
    Space (observed (historyPMF depth) (oldRead depth read)) →L[ℂ]
      Space (observed (historyPMF (depth + 1)) (taggedRead depth read)) :=
  (transfer (historyPMF (depth + 1)) (taggedRead depth read)).comp
    ((normalizedInclusion (Nat.le_succ depth)).toContinuousLinearMap.comp
      (pullback (historyPMF depth) (oldRead depth read)).toContinuousLinearMap)

theorem tagged_decoder_source (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    pullback (historyPMF (depth + 1)) (taggedRead depth read)
      (decoderValue (historyPMF (depth + 1)) (taggedRead depth read)
        (fun atom => if atom.2 then (Real.sqrt (fraction depth (depth + 1)))⁻¹ • value atom.1 else 0)) =
      normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) value) := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  rw [pullback_at _ _ _ actor (source_positive (depth + 1) actor), decoderValue_at _ _ _
    (taggedRead depth read actor) (observed_supported _ _ actor (source_positive (depth + 1) actor))]
  by_cases prior : actor.val < depth + 1
  · let old : Fin (depth + 1) := ⟨actor.val, prior⟩
    have same : includeActor (Nat.le_succ depth) old = actor := Fin.ext rfl
    rw [← same, normalized_prior, pullback_at _ _ _ old (source_positive depth old)]
    change (if decide (old.val < depth + 1) then _ else _) = _
    rw [show decide (old.val < depth + 1) = true from decide_eq_true_eq.mpr old.isLt]
    rfl
  · have last : actor = Fin.last (depth + 1) := Fin.ext (by have bound := actor.isLt; simp only [Fin.val_last]; omega)
    rw [last, normalized_new]
    simp only [taggedRead, priorTag, Fin.val_last, lt_self_iff_false, decide_false, Bool.false_eq_true, if_false]

theorem retained_lift_source (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    pullback (historyPMF (depth + 1)) (taggedRead depth read) (retainedLift depth read value) =
      normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) value) := by
  change pullback (historyPMF (depth + 1)) (taggedRead depth read)
    (transfer (historyPMF (depth + 1)) (taggedRead depth read)
      (normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) value))) = _
  rw [← tagged_decoder_source, IsometricRetainedTransfer.transfer_pullback]

theorem retained_lift_norm (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) : ‖retainedLift depth read value‖ = ‖value‖ := by
  rw [← (pullback (historyPMF (depth + 1)) (taggedRead depth read)).norm_map, retained_lift_source,
    (normalizedInclusion (Nat.le_succ depth)).norm_map, (pullback (historyPMF depth) (oldRead depth read)).norm_map]

omit [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem tagged_forget (depth : Nat) (read : Nat → Observed) : Prod.fst ∘ taggedRead depth read = newRead depth read := rfl

omit [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem tagged_prior (depth : Nat) (read : Nat → Observed) :
    Prod.snd ∘ taggedRead depth read = priorTag depth (depth + 1) := rfl

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
