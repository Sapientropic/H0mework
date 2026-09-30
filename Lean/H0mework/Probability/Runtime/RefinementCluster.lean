import H0mework.Probability.Runtime.RefinementField
import H0mework.Probability.Runtime.InvariantCluster
import Mathlib.Topology.Ultrafilter

/-! Refinement transports and lifts the complete cluster fibres of the same actual history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedObservationRefinement

open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory Filter Topology

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B D : Type u} [AddCommGroup B] [AddCommGroup D]
variable (read : process.State → B) (restriction : B →ₗ[ℤ] D)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : UniformSpace (Field (restrictedRead read restriction)) :=
  fieldUniform (restrictedRead read restriction)
local instance : MeasurableSpace (Field (restrictedRead read restriction)) :=
  fieldBorel (restrictedRead read restriction)
local instance : BorelSpace (Field (restrictedRead read restriction)) := ⟨rfl⟩
local instance : TopologicalSpace.PseudoMetrizableSpace (Field (restrictedRead read restriction)) :=
  field_pseudoMetrizable (restrictedRead read restriction)

def pushCluster (runtime : LivingRuntimeState process) (cluster : HistoryCluster read runtime) :
    HistoryCluster (restrictedRead read restriction) runtime :=
  ⟨cluster.val.map (fieldMap_measurable read restriction).aemeasurable, by
    obtain ⟨ultra, cofinal, converges⟩ := mapClusterPt_iff_ultrafilter.mp cluster.property
    refine mapClusterPt_iff_ultrafilter.mpr ⟨ultra, cofinal, ?_⟩
    have projected := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (empirical read runtime) cluster.val converges (fieldMap_uniformContinuous read restriction).continuous
    simpa only [empirical_pushforward] using projected⟩

variable [Finite B]

theorem pushCluster_surjective (runtime : LivingRuntimeState process) :
    Function.Surjective (pushCluster read restriction runtime) := by
  intro poor
  obtain ⟨ultra, cofinal, poorConverges⟩ := mapClusterPt_iff_ultrafilter.mp poor.property
  let : CompactSpace (ProbabilityMeasure (Field read)) := field_probability_compact read
  obtain ⟨rich, _, richCluster⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure (Field read)))).exists_mapClusterPt
      (f := (ultra : Filter Nat)) (u := empirical read runtime) (by simp)
  have richConverges : Tendsto (empirical read runtime) (ultra : Filter Nat) (𝓝 rich) :=
    (Ultrafilter.clusterPt_iff (f := ultra.map (empirical read runtime))).mp richCluster
  let richPoint : HistoryCluster read runtime := ⟨rich, richCluster.mono cofinal⟩
  have projected := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (empirical read runtime) rich richConverges (fieldMap_uniformContinuous read restriction).continuous
  simp only [empirical_pushforward] at projected
  refine ⟨richPoint, ?_⟩
  apply Subtype.ext
  exact tendsto_nhds_unique projected poorConverges

end
end SourceGeneratedObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
