import H0mework.Probability.Empirical.ConditionalFormula
import H0mework.Realization.Operations.ObservationNative
import H0mework.Probability.EmpiricalRecovery.Fibre

/-! Conditional next fibres are exactly the existing autonomous model fibres of the same actual actors. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery

open SourceConditionalTransfer SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceOperationNative.Observed

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

theorem nextAtom_is_observed_point (index : Fin (bound + 1)) :
    nextAtom read runtime bound index =
      observedPoint (process := process) read ((history runtime bound).stageAt index).next := by
  rw [nextAtom, fieldSample, fieldPoint_action]
  rfl

theorem nextAtom_model_iff (left right : Fin (bound + 1)) :
    nextAtom read runtime bound left = nextAtom read runtime bound right ↔
      modelPoint (process := process) read ((history runtime bound).stageAt left).next =
        modelPoint (process := process) read ((history runtime bound).stageAt right).next := by
  rw [nextAtom_is_observed_point, nextAtom_is_observed_point]
  exact (native_fibre_iff (process := process) read
    ((history runtime bound).stageAt left).next ((history runtime bound).stageAt right).next).trans
      (model_native_fibre_iff (process := process) read
        ((history runtime bound).stageAt left).next ((history runtime bound).stageAt right).next).symm

theorem nextAtom_future_iff (left right : Fin (bound + 1)) :
    nextAtom read runtime bound left = nextAtom read runtime bound right ↔
      ∀ stage : Nat,
        read (((history runtime bound).stageAt left).next.advance stage).state =
          read (((history runtime bound).stageAt right).next.advance stage).state :=
  (nextAtom_model_iff read runtime bound left right).trans
    (model_native_fibre_iff (process := process) read
      ((history runtime bound).stageAt left).next ((history runtime bound).stageAt right).next)

theorem nextAtom_supported (index : Fin (bound + 1)) :
    nextAtom read runtime bound index ∈ (fieldPMF read runtime.tick.next bound).support := by
  rw [nextPMF_from_indices]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨index, by simp [historyPMF], rfl⟩

theorem conditional_model_fibre (query index : Fin (bound + 1)) :
    index ∈ (conditionalIndices read runtime bound (nextAtom read runtime bound query)
        (nextAtom_supported read runtime bound query)).support ↔
      modelPoint (process := process) read ((history runtime bound).stageAt index).next =
        modelPoint (process := process) read ((history runtime bound).stageAt query).next :=
  (conditionalIndices_support_iff read runtime bound _ _ index).trans
    (nextAtom_model_iff read runtime bound index query)

theorem zero_residual_iff_model (value : Space read runtime bound) :
    residual read runtime bound value = 0 ↔
      ∀ first second : Fin (bound + 1),
        modelPoint (process := process) read ((history runtime bound).stageAt first).next =
          modelPoint (process := process) read ((history runtime bound).stageAt second).next →
        value (fieldSample read runtime bound first) = value (fieldSample read runtime bound second) := by
  rw [zero_residual_iff_fibre]
  constructor
  · intro constant first second same
    exact constant first second ((nextAtom_model_iff read runtime bound first second).mpr same)
  · intro constant first second same
    exact constant first second ((nextAtom_model_iff read runtime bound first second).mp same)

end
end SourceConditionalRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
