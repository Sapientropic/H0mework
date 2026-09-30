import H0mework.Probability.EmpiricalRecovery.ActorError

/-! The actor adjoint consumes the already generated complete conditional PMF at the current field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer MeasureTheory
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

private theorem transfer_pushforward {Source Observed : Type*} [Fintype Source]
    [MeasurableSpace Source] [MeasurableSingletonClass Source]
    [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
    (source : PMF Source) (observer : Source → Observed) (target : PMF Observed)
    (same : target = observed source observer)
    (preserved : MeasurePreserving observer source.toMeasure target.toMeasure)
    (task : Source → ℂ) (atom : Observed) :
    IsometricRetainedTransfer.transfer (Lp.compMeasurePreservingₗᵢ ℂ observer preserved)
        (taskValue source task) atom = optimalDecoder source observer task atom := by
  subst target
  rfl

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

theorem actorTransfer_is_conditional (task : Fin (bound + 1) → ℂ) (atom : Field read) :
    actorTransfer read runtime bound (taskValue (historyPMF bound) task) atom =
      optimalDecoder (historyPMF bound) (fieldSample read runtime bound) task atom :=
  transfer_pushforward (historyPMF bound) (fieldSample read runtime bound) (fieldPMF read runtime bound)
    (fieldPMF_from_indices read runtime bound) (actor_measurePreserving read runtime bound) task atom

theorem actor_fibre_formula (task : Fin (bound + 1) → ℂ) (atom : Field read)
    (supported : atom ∈ (observed (historyPMF bound) (fieldSample read runtime bound)).support) :
    actorTransfer read runtime bound (taskValue (historyPMF bound) task) atom =
      ∑ index : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) (fieldSample read runtime bound) atom supported index).toReal • task index :=
  (actorTransfer_is_conditional read runtime bound task atom).trans
    (optimal_is_conditional (historyPMF bound) (fieldSample read runtime bound) task atom supported)

theorem completeTransfer_is_conditional (task : Fin (bound + 1) → ℂ) (atom : Field read) :
    SourceGeneratedEmpiricalHilbert.transfer read runtime bound
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) atom =
      optimalDecoder (historyPMF bound) (nextAtom read runtime bound) task atom := by
  have composition := IsometricRetainedTransfer.transfer_comp (actorPullback read runtime bound)
    (SourceGeneratedEmpiricalHilbert.pullback read runtime bound)
  have source := congrArg IsometricRetainedTransfer.transfer (nextPullback_is_source_map read runtime bound)
  have readback := congrArg (fun operation : ActorSpace bound →L[ℂ]
      SourceGeneratedEmpiricalHilbert.Space read runtime.tick.next bound => operation (taskValue (historyPMF bound) task) atom)
    (composition.symm.trans source)
  exact readback.trans (transfer_pushforward (historyPMF bound) (nextAtom read runtime bound)
    (fieldPMF read runtime.tick.next bound) (nextPMF_from_indices read runtime bound)
    (next_measurePreserving read runtime bound) task atom)

theorem source_actor_minimum (task : Fin (bound + 1) → ℂ) :
    ‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 =
      error (historyPMF bound) (fieldSample read runtime bound) task
        (fun atom => actorTransfer read runtime bound (taskValue (historyPMF bound) task) atom) := by
  have residualEq : actorResidual read runtime bound (taskValue (historyPMF bound) task) =
      taskValue (historyPMF bound) task - actorPullback read runtime bound
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) := rfl
  rw [residualEq, norm_source_sq]
  apply Finset.sum_congr rfl
  intro index _
  have supported : index ∈ (historyPMF bound).support := by simp [historyPMF]
  have evaluated := (evalAt (historyPMF bound) index supported).map_sub
    (taskValue (historyPMF bound) task)
    (actorPullback read runtime bound (actorTransfer read runtime bound (taskValue (historyPMF bound) task)))
  change (taskValue (historyPMF bound) task - actorPullback read runtime bound
      (actorTransfer read runtime bound (taskValue (historyPMF bound) task))) index =
    taskValue (historyPMF bound) task index - actorPullback read runtime bound
      (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) index at evaluated
  rw [evaluated, taskValue_at _ _ _ supported, actorPullback_at]

end
end SourceWeightedRecovery.Runtime.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
