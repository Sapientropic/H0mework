import H0mework.Probability.EmpiricalRecovery.FiniteConditional
import H0mework.Probability.EmpiricalRecovery.ActorConditional

/-! Finite raw queries directly read the original actor-to-field-to-next transfer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer SourceWeightedRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (windowBound : Nat) (runtime : LivingRuntimeState process) (actorBound : Nat)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

abbrev fieldRead : Field read →ₗ[ℤ] (Fin (windowBound + 1) → B) :=
  stageRead (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read) windowBound

theorem fieldRead_query (index : Fin (actorBound + 1)) :
    fieldRead read windowBound (nextAtom read runtime actorBound index) = query read windowBound runtime actorBound index := by
  rw [SourceConditionalRecovery.nextAtom_is_observed_point]
  funext sample
  exact SourceOperationNative.Observed.observedPoint_read (process := process) read
    ((history runtime actorBound).stageAt index).next windowBound sample

theorem finiteError_is_original (task : Fin (actorBound + 1) → ℂ) (decoder : (Fin (windowBound + 1) → B) → ℂ) :
    error (historyPMF actorBound) (query read windowBound runtime actorBound) task decoder =
      Runtime.Actor.rawError read runtime actorBound task (fun atom => decoder (fieldRead read windowBound atom)) := by
  unfold Runtime.Actor.rawError error
  apply Finset.sum_congr rfl
  intro index _
  dsimp only
  rw [fieldRead_query]

variable (coefficients : Fin (windowBound + 1) → ℤ)
variable (sourceLaw : (SourceOperationNative.observer process read).comp
    (SourceOperationNative.sourceAction process ^ (windowBound + 1)) =
      ∑ index : Fin (windowBound + 1), coefficients index •
        stageEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read) index.val)

include sourceLaw

theorem completeTransfer_finite (task : Fin (actorBound + 1) → ℂ) (index : Fin (actorBound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer read runtime actorBound
        (Runtime.Actor.actorTransfer read runtime actorBound (taskValue (historyPMF actorBound) task))
        (nextAtom read runtime actorBound index) =
      ∑ candidate : Fin (actorBound + 1),
        (conditional read windowBound runtime actorBound index candidate).toReal • task candidate := by
  rw [conditional_is_original read windowBound runtime actorBound coefficients sourceLaw index]
  exact (Runtime.Actor.completeTransfer_is_conditional read runtime actorBound task (nextAtom read runtime actorBound index)).trans
    (optimal_is_conditional (historyPMF actorBound) (nextAtom read runtime actorBound) task
      (nextAtom read runtime actorBound index) (by
        change nextAtom read runtime actorBound index ∈ ((historyPMF actorBound).map (nextAtom read runtime actorBound)).support
        rw [← nextPMF_from_indices]
        exact SourceConditionalRecovery.nextAtom_supported read runtime actorBound index))

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
