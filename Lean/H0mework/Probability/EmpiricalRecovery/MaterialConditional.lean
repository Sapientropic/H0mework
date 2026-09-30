import H0mework.Probability.EmpiricalRecovery.MaterialNative
import H0mework.Probability.EmpiricalRecovery.FiniteTransfer

/-! The generated material recurrence makes the same finite query consume the original complete conditional law and transfer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.MaterialRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer SourceWeightedRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory

noncomputable section

universe r u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] [Nontrivial R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
variable [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B) (material : Nat → C)
variable (generated : ∀ stage : Nat, material (stage + 1) = action (material stage))
variable (read : process.State → B) (runtime : LivingRuntimeState process)
variable (read_source : ∀ stage : Nat, read (runtime.advance stage).state = observation (material stage))

include generated read_source

theorem conditional_is_original (actorBound : Nat) (index : Fin (actorBound + 1)) :
    FiniteRecurrence.Native.conditional read (bound action) runtime actorBound index =
      conditionalIndices read runtime actorBound (nextAtom read runtime actorBound index)
        (SourceConditionalRecovery.nextAtom_supported read runtime actorBound index) := by
  have sameFibre :
      {candidate | FiniteRecurrence.Native.query read (bound action) runtime actorBound candidate =
        FiniteRecurrence.Native.query read (bound action) runtime actorBound index} =
      {candidate | nextAtom read runtime actorBound candidate = nextAtom read runtime actorBound index} := by
    ext candidate
    exact (query_fibre_iff action observation material generated read runtime read_source actorBound candidate index).symm
  unfold FiniteRecurrence.Native.conditional conditionalIndices SourceConditionalHistory.conditional
  congr 1

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

theorem completeTransfer_finite (actorBound : Nat) (task : Fin (actorBound + 1) → ℂ) (index : Fin (actorBound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer read runtime actorBound
        (Runtime.Actor.actorTransfer read runtime actorBound (taskValue (historyPMF actorBound) task))
        (nextAtom read runtime actorBound index) =
      ∑ candidate : Fin (actorBound + 1),
        (FiniteRecurrence.Native.conditional read (bound action) runtime actorBound index candidate).toReal • task candidate := by
  rw [conditional_is_original action observation material generated read runtime read_source actorBound index]
  exact (Runtime.Actor.completeTransfer_is_conditional read runtime actorBound task (nextAtom read runtime actorBound index)).trans
    (optimal_is_conditional (historyPMF actorBound) (nextAtom read runtime actorBound) task
      (nextAtom read runtime actorBound index) (by
        change nextAtom read runtime actorBound index ∈ ((historyPMF actorBound).map (nextAtom read runtime actorBound)).support
        rw [← nextPMF_from_indices]
        exact SourceConditionalRecovery.nextAtom_supported read runtime actorBound index))

end
end SourceGeneratedActionObservationHistory.MaterialRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
