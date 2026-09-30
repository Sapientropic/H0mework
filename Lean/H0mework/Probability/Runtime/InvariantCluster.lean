import H0mework.Realization.HistoryTopology.Compactness
import H0mework.Probability.Runtime.InvariantMoments
import Mathlib.Topology.Ultrafilter

/-! An actual empirical-history cluster is preserved by the original field action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology.NativeProbability

open MeasureTheory Filter Topology
open SourceOperationNative SourceGeneratedRuntimeHistoryProbability
open scoped BoundedContinuousFunction

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : TopologicalSpace.PseudoMetrizableSpace (Field read) := field_pseudoMetrizable read

theorem cluster_measurePreserving (runtime : LivingRuntimeState process)
    (limit : ProbabilityMeasure (Field read))
    (cluster : MapClusterPt limit atTop (empirical read runtime)) :
    MeasurePreserving (fieldAction read) (limit : Measure (Field read)) (limit : Measure (Field read)) := by
  obtain ⟨ultra, cofinal, converges⟩ := mapClusterPt_iff_ultrafilter.mp cluster
  have actionContinuous : Continuous (fieldAction read) :=
    (endomorphism_uniformContinuous (sourceAction process) (observer process read)).continuous
  have mapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (empirical read runtime) limit converges actionContinuous
  have preserved :
      (limit.map (fieldAction_measurable read).aemeasurable).toFiniteMeasure = limit.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    have before := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp converges) f
    have after := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp mapped) f
    have difference := after.sub before
    simp only [empirical_map] at difference
    have vanishes := (empirical_drift_tendsto_zero read runtime f).mono_left cofinal
    exact sub_eq_zero.mp (tendsto_nhds_unique difference vanishes)
  refine ⟨fieldAction_measurable read, ?_⟩
  exact congrArg (fun measure : FiniteMeasure (Field read) => (measure : Measure (Field read))) preserved

/-- The complete source-indexed cluster fibre retains every possible limiting measure. -/
abbrev HistoryCluster (runtime : LivingRuntimeState process) :=
  {measure : ProbabilityMeasure (Field read) // MapClusterPt measure atTop (empirical read runtime)}

theorem historyCluster_measurePreserving (runtime : LivingRuntimeState process)
    (cluster : HistoryCluster read runtime) :
    MeasurePreserving (fieldAction read)
      (cluster.val : Measure (Field read)) (cluster.val : Measure (Field read)) :=
  cluster_measurePreserving read runtime cluster.val cluster.property

variable [Finite B]

theorem exists_invariant_history_measure (runtime : LivingRuntimeState process) :
    ∃ limit : ProbabilityMeasure (Field read),
      MapClusterPt limit atTop (empirical read runtime) ∧
        MeasurePreserving (fieldAction read) (limit : Measure (Field read)) (limit : Measure (Field read)) := by
  let : CompactSpace (ProbabilityMeasure (Field read)) := field_probability_compact read
  obtain ⟨limit, _, cluster⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure (Field read)))).exists_mapClusterPt
      (f := atTop) (u := empirical read runtime) (by simp)
  exact ⟨limit, cluster, cluster_measurePreserving read runtime limit cluster⟩

theorem historyCluster_nonempty (runtime : LivingRuntimeState process) :
    Nonempty (HistoryCluster read runtime) := by
  obtain ⟨measure, cluster, _⟩ := exists_invariant_history_measure read runtime
  exact ⟨⟨measure, cluster⟩⟩

end
end SourceGeneratedScalarCofinalTopology.NativeProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
