import H0mework.Versions.X.Fock.CopyGraph.BirthObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedAtomicObservation SourceUniformFibreVariance SourceHistoryGrowth
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead taggedRead)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def direction (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier :=
  SourceGraphGrowth.newResidual depth index read (SourceGraphBirth.fresh depth index)

def rawValue (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    Space (observed (historyPMF (depth + 1)) (newRead depth read)) :=
  -- The retained value is read only at atoms supported by the actual old inventory.
  decoderValue (historyPMF (depth + 1)) (newRead depth read) (fun atom =>
    if atom ∈ atoms (historyPMF depth) (oldRead depth read) then
      (Real.sqrt (fraction depth (depth + 1)))⁻¹ • SourceGraphBirth.priorValue depth read value atom
    else 0)

theorem raw_prior (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read)))
    (actor : Fin (depth + 1)) :
    rawValue depth read value (oldRead depth read actor) = value (oldRead depth read actor, true) := by
  have prior := observed_supported (historyPMF depth) (oldRead depth read) actor (source_positive depth actor)
  have supported : oldRead depth read actor ∈ (observed (historyPMF (depth + 1)) (newRead depth read)).support :=
    observed_supported (historyPMF (depth + 1)) (newRead depth read) (includeActor (Nat.le_succ depth) actor) (source_positive (depth + 1) _)
  rw [rawValue, decoderValue_at _ _ _ _ supported, if_pos ((atoms_iff _ _ _).mpr prior), SourceGraphBirth.priorValue,
    decoderValue_at _ _ _ _ prior, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (fraction_pos depth (depth + 1))).ne', one_smul]

def correction (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) : ℂ :=
  value (taggedRead depth read (Fin.last (depth + 1))) - rawValue depth read value (newRead depth read (Fin.last (depth + 1)))

theorem source_decomposition (depth : Nat) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    pullback (historyPMF (depth + 1)) (taggedRead depth read) value =
      pullback (historyPMF (depth + 1)) (newRead depth read) (rawValue depth read value) +
        correction depth read value • cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)) := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  change evalAt (historyPMF (depth + 1)) actor (source_positive (depth + 1) actor)
    (pullback (historyPMF (depth + 1)) (taggedRead depth read) value) =
    evalAt (historyPMF (depth + 1)) actor (source_positive (depth + 1) actor)
      (pullback (historyPMF (depth + 1)) (newRead depth read) (rawValue depth read value) +
        correction depth read value • cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))
  rw [map_add, map_smul]
  change (pullback (historyPMF (depth + 1)) (taggedRead depth read) value) actor =
    (pullback (historyPMF (depth + 1)) (newRead depth read) (rawValue depth read value)) actor +
      correction depth read value * cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)) actor
  rw [pullback_at _ _ _ actor (source_positive (depth + 1) actor),
    pullback_at _ _ _ actor (source_positive (depth + 1) actor), cotest_value]
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
    rw [← same, if_neg distinct, mul_zero, add_zero, tag]
    exact (raw_prior depth read value before).symm
  · have last : actor = Fin.last (depth + 1) := Fin.ext (by have bound := actor.isLt; simp only [Fin.val_last]; omega)
    rw [last, if_pos rfl, mul_one, correction]
    abel

theorem action_decomposition (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (taggedRead depth read))) :
    SourceGraphGrowth.taggedAction depth index read value = SourceGraphGrowth.newAction depth index read (rawValue depth read value) +
      correction depth read value • SourceGraphBirth.fresh depth index := by
  rw [SourceConditionalGraphDecoder.action_source, source_decomposition, map_add, map_smul,
    ← SourceConditionalGraphDecoder.action_source]
  rfl

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
