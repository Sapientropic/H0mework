import H0mework.Versions.X.Fock.HistoryModel.DynamicConsumer
import H0mework.Versions.X.Probability.Recovery.Refinement
import H0mework.Realization.HilbertTransfer.Composition

/-! The original cofinal topology makes the generated dynamic-word restriction measurable. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceGeneratedScalarCofinalTopology

noncomputable section

@[instance_reducible] def uniform (depth : Nat) : UniformSpace (Complete.Carrier depth) :=
  observationUniform (wordData depth) (wordLaws depth)

@[instance_reducible] def measurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) :=
  @borel (Complete.Carrier depth) (uniform depth).toTopologicalSpace

theorem field_t2 (depth : Nat) : @T2Space (Complete.Carrier depth) (uniform depth).toTopologicalSpace := by
  let tower := wordData depth
  let laws := wordLaws depth
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  let : UniformSpace (tower.Completion laws) := observationUniform tower laws
  exact (coordinates_isUniformEmbedding tower laws).isEmbedding.t2Space

theorem previous_uniform (depth : Nat) :
    @UniformContinuous _ _ (uniform (depth + 1)) (uniform depth) (previous depth) :=
  completionMorphism_uniformContinuous (morphism depth) (wordLaws (depth + 1)) (wordLaws depth)

theorem previous_measurable (depth : Nat) :
    @Measurable _ _ (measurable (depth + 1)) (measurable depth) (previous depth) := by
  let : UniformSpace (Complete.Carrier (depth + 1)) := uniform (depth + 1)
  let : UniformSpace (Complete.Carrier depth) := uniform depth
  exact (previous_uniform depth).continuous.borel_measurable

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
