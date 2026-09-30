import H0mework.Realization.HistoryTopology.Probability
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Basic

/-! Finite observation letters make the existing closed observation field compact. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology.NativeProbability

open SourceOperationNative SourceGeneratedActionObservationHistory MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

theorem field_t2 : @T2Space (Field read) (fieldUniform read).toTopologicalSpace := by
  let tower := data (sourceAction process) (observer process read)
  let laws := compatible (sourceAction process) (observer process read)
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  let : UniformSpace (Field read) := fieldUniform read
  exact (coordinates_isUniformEmbedding tower laws).isEmbedding.t2Space

theorem field_pseudoMetrizable :
    @TopologicalSpace.PseudoMetrizableSpace (Field read) (fieldUniform read).toTopologicalSpace := by
  let tower := data (sourceAction process) (observer process read)
  let laws := compatible (sourceAction process) (observer process read)
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  let : UniformSpace (Field read) := fieldUniform read
  exact (coordinates_isUniformEmbedding tower laws).isEmbedding.isInducing.pseudoMetrizableSpace

variable [Finite B]

theorem field_stage_finite (stage : Nat) :
    Finite ((data (sourceAction process) (observer process read)).StageQuotient stage) :=
  Finite.of_injective _ ((data (sourceAction process) (observer process read)).stageRealization_injective stage)

theorem field_compact : @CompactSpace (Field read) (fieldUniform read).toTopologicalSpace := by
  let tower := data (sourceAction process) (observer process read)
  let laws := compatible (sourceAction process) (observer process read)
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  let : ∀ stage, Finite (tower.StageQuotient stage) := field_stage_finite read
  let : UniformSpace (Field read) := fieldUniform read
  have closedEmbedding : Topology.IsClosedEmbedding (coordinates tower laws) :=
    ⟨(coordinates_isUniformEmbedding tower laws).isEmbedding, coordinates_isClosed tower laws⟩
  exact closedEmbedding.compactSpace

theorem field_secondCountable :
    @SecondCountableTopology (Field read) (fieldUniform read).toTopologicalSpace := by
  let tower := data (sourceAction process) (observer process read)
  let laws := compatible (sourceAction process) (observer process read)
  let : ∀ stage, UniformSpace (tower.StageQuotient stage) := stageUniform tower
  let : ∀ stage, Finite (tower.StageQuotient stage) := field_stage_finite read
  let : UniformSpace (Field read) := fieldUniform read
  exact (coordinates_isUniformEmbedding tower laws).isEmbedding.secondCountableTopology

theorem field_probability_compact :
    letI : UniformSpace (Field read) := fieldUniform read
    letI : MeasurableSpace (Field read) := fieldBorel read
    letI : BorelSpace (Field read) := ⟨rfl⟩
    CompactSpace (ProbabilityMeasure (Field read)) := by
  let : UniformSpace (Field read) := fieldUniform read
  let : MeasurableSpace (Field read) := fieldBorel read
  let : BorelSpace (Field read) := ⟨rfl⟩
  let : T2Space (Field read) := field_t2 read
  let : CompactSpace (Field read) := field_compact read
  infer_instance

end
end SourceGeneratedScalarCofinalTopology.NativeProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
