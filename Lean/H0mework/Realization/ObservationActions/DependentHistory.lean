import H0mework.Realization.Operations.ObservationModel
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent

open SourceGeneratedActionObservationHistory (PrefixCarrier prefixRestriction dropFirst dropFirst_transition)
open SourceGeneratedScalarCofinalKernelCompletion SourceGeneratedScalarCofinalNaturality
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u v

variable {𝕜 : Type r} [NontriviallyNormedField 𝕜]
variable {State : Type v} (step : State → State) {C : State → Type u} {B : Type u}
variable [∀ state, NormedAddCommGroup (C state)] [∀ state, NormedSpace 𝕜 (C state)]
variable [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : ∀ state, C state →L[𝕜] C (step state))
variable (observation : ∀ state, C state →L[𝕜] B)

def stageEvaluator (state : State) : Nat → C state →L[𝕜] B
  | 0 => observation state
  | stage + 1 => (stageEvaluator (step state) stage).comp (action state)

def prefixEvaluator (state : State) (bound : Nat) : C state →ₗ[𝕜] PrefixCarrier B bound :=
  LinearMap.pi fun index => (stageEvaluator step action observation state index.val).toLinearMap

def data (state : State) : Data (R := 𝕜) (Generator := C state) (Carrier := PrefixCarrier B) where
  evaluator := prefixEvaluator step action observation state
  transition := prefixRestriction

theorem compatible (state : State) : (data step action observation state).Compatible := by
  intro bound
  rfl

def historyMorphism (state : State) :
    Morphism (SourceGeneratedScalarCofinalTail.tail (data step action observation state))
      (data step action observation (step state)) where
  generatorMap := (action state).toLinearMap
  stageMap := dropFirst
  transition_naturality := dropFirst_transition
  evaluator_naturality := by
    intro bound
    ext value index
    rfl

def completion (state : State) :=
  (data step action observation state).Completion (compatible step action observation state)

def sourceMap (state : State) : C state →ₗ[𝕜] completion step action observation state :=
  ((data step action observation state).completionMap (compatible step action observation state)).hom

def nextCompletion (state : State) :
    completion step action observation state →ₗ[𝕜] completion step action observation (step state) :=
  ((historyMorphism step action observation state).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data step action observation state)
      (compatible step action observation state))
    (compatible step action observation (step state))).hom.comp
      (SourceGeneratedScalarCofinalTail.completionMap (data step action observation state)
        (compatible step action observation state)).hom

theorem next_source (state : State) (value : C state) :
    nextCompletion step action observation state (sourceMap step action observation state value) =
      sourceMap step action observation (step state) (action state value) := by
  have tail := ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_source (data step action observation state)
      (compatible step action observation state)) value
  have source := ConcreteCategory.congr_hom
    ((historyMorphism step action observation state).completionMorphism_source_naturality
      (SourceGeneratedScalarCofinalTail.compatible (data step action observation state)
        (compatible step action observation state))
      (compatible step action observation (step state))) value
  exact (congrArg ((historyMorphism step action observation state).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible (data step action observation state)
      (compatible step action observation state))
    (compatible step action observation (step state))).hom tail).trans source

end
end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
