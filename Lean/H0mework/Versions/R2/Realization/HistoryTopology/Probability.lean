import H0mework.Realization.HistoryTopology.ObservedAction
import H0mework.Versions.R2.Realization.Operations.NativeState
import H0mework.Versions.R2.Probability.Runtime.Transition
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Finite native history sampling is pushed through the existing continuous observation action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology.NativeProbability

open SourceOperationNative SourceGeneratedActionObservationHistory
open SourceGeneratedRuntimeHistoryProbability MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

abbrev Field := (data (sourceAction process) (observer process read)).Completion
  (compatible (sourceAction process) (observer process read))

def fieldPoint (state : process.State) : Field read :=
  sourceMap (sourceAction process) (observer process read) (statePoint process state)

abbrev fieldAction : Field read →ₗ[ℤ] Field read :=
  endomorphism (sourceAction process) (observer process read)

theorem fieldPoint_action (state : process.State) :
    fieldAction read (fieldPoint read state) = fieldPoint read (process.successor state) := by
  exact (endomorphism_source (sourceAction process) (observer process read) (statePoint process state)).trans
    (congrArg (sourceMap (sourceAction process) (observer process read)) (sourceAction_statePoint process state))

def fieldPMF (runtime : LivingRuntimeState process) (bound : Nat) : PMF (Field read) :=
  (statePMF runtime bound).map (fieldPoint read)

theorem fieldPMF_support_iff (runtime : LivingRuntimeState process) (bound : Nat) (value : Field read) :
    value ∈ (fieldPMF read runtime bound).support ↔
      ∃ index : Fin (bound + 1), fieldPoint read (sample runtime bound index) = value := by
  rw [fieldPMF, statePMF, PMF.map_comp, PMF.mem_support_map_iff]
  simp only [historyPMF, PMF.mem_support_uniformOfFintype, true_and, Function.comp_apply]

theorem fieldPMF_action (runtime : LivingRuntimeState process) (bound : Nat) :
    (fieldPMF read runtime bound).map (fieldAction read) = fieldPMF read runtime.tick.next bound := by
  rw [fieldPMF, PMF.map_comp]
  have square : (fieldAction read ∘ fieldPoint read) = fieldPoint read ∘ process.successor :=
    funext (fieldPoint_action read)
  rw [square, ← PMF.map_comp, statePMF_successor]
  rfl

@[instance_reducible] def fieldUniform : UniformSpace (Field read) :=
  observationUniform (data (sourceAction process) (observer process read))
    (compatible (sourceAction process) (observer process read))

@[instance_reducible] def fieldBorel : MeasurableSpace (Field read) :=
  @borel (Field read) (fieldUniform read).toTopologicalSpace

theorem fieldAction_measurable :
    @Measurable _ _ (fieldBorel read) (fieldBorel read) (fieldAction read) := by
  let : UniformSpace (Field read) := fieldUniform read
  exact (endomorphism_uniformContinuous (sourceAction process) (observer process read)).continuous.borel_measurable

theorem fieldMeasure_next (runtime : LivingRuntimeState process) (bound : Nat) :
    letI : MeasurableSpace (Field read) := fieldBorel read
    (fieldPMF read runtime bound).toMeasure.map (fieldAction read) =
      (fieldPMF read runtime.tick.next bound).toMeasure := by
  let : MeasurableSpace (Field read) := fieldBorel read
  rw [PMF.toMeasure_map (fieldAction read) (fieldPMF read runtime bound) (fieldAction_measurable read),
    fieldPMF_action]

end
end SourceGeneratedScalarCofinalTopology.NativeProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
