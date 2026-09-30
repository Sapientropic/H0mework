import H0mework.Realization.HistoryTopology.Continuity
import H0mework.Realization.Operations.ObservationHistory

/-! The original observation history action is continuous on its entire existing completion. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]

open SourceGeneratedActionObservationHistory

theorem endomorphism_uniformContinuous (action : C →ₗ[R] C) (observation : C →ₗ[R] B) :
    @UniformContinuous _ _
      (observationUniform (data action observation) (compatible action observation))
      (observationUniform (data action observation) (compatible action observation))
      (endomorphism action observation) := by
  let : UniformSpace ((data action observation).Completion (compatible action observation)) :=
    observationUniform (data action observation) (compatible action observation)
  let : UniformSpace ((SourceGeneratedScalarCofinalTail.tail (data action observation)).Completion
      (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))) :=
    observationUniform (SourceGeneratedScalarCofinalTail.tail (data action observation))
      (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
  exact (completionMorphism_uniformContinuous (historyMorphism action observation)
    (SourceGeneratedScalarCofinalTail.compatible (data action observation) (compatible action observation))
    (compatible action observation)).comp
      (tail_uniformContinuous (data action observation) (compatible action observation))

end
end SourceGeneratedScalarCofinalTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
