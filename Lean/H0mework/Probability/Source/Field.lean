import H0mework.Realization.HistoryTopology.ObservedAction
import H0mework.Probability.Runtime.History
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Native successor and observation primitives generate their field and finite empirical update. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory

open SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalTopology MeasureTheory

noncomputable section

universe u

variable {State B : Type u} [AddCommGroup B]

abbrev Carrier (State : Type u) := State →₀ ℤ

def sourcePoint (state : State) : Carrier State := Finsupp.single state 1

def sourceAction (step : State → State) : Carrier State →ₗ[ℤ] Carrier State :=
  Finsupp.lmapDomain ℤ ℤ step

def observation (read : State → B) : Carrier State →ₗ[ℤ] B :=
  Finsupp.linearCombination ℤ read

@[simp] theorem sourceAction_point (step : State → State) (state : State) :
    sourceAction step (sourcePoint state) = sourcePoint (step state) := by
  simp only [sourceAction, sourcePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

@[simp] theorem observation_point (read : State → B) (state : State) :
    observation read (sourcePoint state) = read state := by
  simp only [observation, sourcePoint, Finsupp.linearCombination_single, one_smul]

variable (step : State → State) (read : State → B)

abbrev Field := (data (sourceAction step) (observation read)).Completion
  (compatible (sourceAction step) (observation read))

def fieldPoint (state : State) : Field step read :=
  sourceMap (sourceAction step) (observation read) (sourcePoint state)

abbrev fieldAction : Field step read →ₗ[ℤ] Field step read :=
  endomorphism (sourceAction step) (observation read)

theorem fieldPoint_action (state : State) :
    fieldAction step read (fieldPoint step read state) = fieldPoint step read (step state) :=
  (endomorphism_source (sourceAction step) (observation read) (sourcePoint state)).trans
    (congrArg (sourceMap (sourceAction step) (observation read)) (sourceAction_point step state))

@[instance_reducible] def fieldUniform : UniformSpace (Field step read) :=
  observationUniform (data (sourceAction step) (observation read))
    (compatible (sourceAction step) (observation read))

@[instance_reducible] def fieldBorel : MeasurableSpace (Field step read) :=
  @borel (Field step read) (fieldUniform step read).toTopologicalSpace

theorem fieldAction_measurable :
    @Measurable _ _ (fieldBorel step read) (fieldBorel step read) (fieldAction step read) := by
  let : UniformSpace (Field step read) := fieldUniform step read
  exact (endomorphism_uniformContinuous (sourceAction step) (observation read)).continuous.borel_measurable

def statePMF (state : State) (bound : Nat) : PMF State :=
  (SourceGeneratedRuntimeHistoryProbability.historyPMF bound).map fun index => step^[index.val] state

theorem statePMF_step (state : State) (bound : Nat) :
    (statePMF step state bound).map step = statePMF step (step state) bound := by
  rw [statePMF, PMF.map_comp, statePMF]
  congr 1
  funext index
  exact (Function.iterate_succ_apply' step index.val state).symm.trans
    (Function.iterate_succ_apply step index.val state)

def fieldPMF (state : State) (bound : Nat) : PMF (Field step read) :=
  (statePMF step state bound).map (fieldPoint step read)

theorem fieldPMF_action (state : State) (bound : Nat) :
    (fieldPMF step read state bound).map (fieldAction step read) =
      fieldPMF step read (step state) bound := by
  rw [fieldPMF, PMF.map_comp]
  have square : fieldAction step read ∘ fieldPoint step read = fieldPoint step read ∘ step :=
    funext (fieldPoint_action step read)
  rw [square, ← PMF.map_comp, statePMF_step]
  rfl

local instance : MeasurableSpace (Field step read) := fieldBorel step read

def empirical (state : State) (bound : Nat) : ProbabilityMeasure (Field step read) :=
  ⟨(fieldPMF step read state bound).toMeasure, inferInstance⟩

theorem empirical_map (state : State) (bound : Nat) :
    (empirical step read state bound).map (fieldAction_measurable step read).aemeasurable =
      empirical step read (step state) bound := by
  apply ProbabilityMeasure.toMeasure_injective
  change (fieldPMF step read state bound).toMeasure.map (fieldAction step read) = _
  rw [PMF.toMeasure_map _ _ (fieldAction_measurable step read), fieldPMF_action]
  rfl

end
end SourceOwnedObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
