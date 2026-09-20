import H0mework.Physics.MotherLaws.RestrictionEmbeddingDistances
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding

open Set Filter Topology TopologicalSpace Metric
open scoped Topology
open MotherStreamLaws

noncomputable section

/-- This local metric preserves the pre-existing product uniformity and topology. -/
local instance streamMetric : MetricSpace Stream := UniformSpace.metricSpace Stream

theorem smallCoordinate_open (k : ℕ) : IsOpen (smallCoordinate k) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨n, small⟩
  exact Filter.mem_of_superset ((isOpen_lt (continuous_apply n) continuous_const).mem_nhds small)
    (fun z hz => ⟨n, hz⟩)

theorem smallCoordinate_compl_nonempty (k : ℕ) : (smallCoordinate k)ᶜ.Nonempty := by
  refine ⟨fun _ => 1 / (k + 1 : ℝ), ?_⟩
  simp [smallCoordinate]

def gap (k : ℕ) (y : Stream) : ℝ := infDist y (smallCoordinate k)ᶜ

theorem gap_continuous (k : ℕ) : Continuous (gap k) := continuous_infDist_pt _

theorem gap_pos_iff (k : ℕ) (y : Stream) : y ∈ smallCoordinate k ↔ 0 < gap k y := by
  simpa only [gap, notMem_compl_iff] using
    (smallCoordinate_open k).isClosed_compl.notMem_iff_infDist_pos (smallCoordinate_compl_nonempty k)

variable (X : Type*) [MetricSpace X] [SeparableSpace X] [Nonempty X]

def guard (x : X) : Stream := fun k => (gap k (distances X x))⁻¹

theorem guard_continuous : Continuous (guard X) := by
  apply continuous_pi
  intro k
  exact ((gap_continuous k).comp (distances_continuous X)).inv₀
    (fun x => ne_of_gt ((gap_pos_iff k _).mp (distances_small X x k)))

def graph (x : X) : Stream × Stream := (distances X x, guard X x)

def closedCarrier : Set (Stream × Stream) :=
  {state | state.1 ∈ closure (Set.range (distances X)) ∧
    ∀ k, gap k state.1 * state.2 k = 1}

theorem closedCarrier_isClosed : IsClosed (closedCarrier X) := by
  simp only [closedCarrier, ofPred_and, ofPred_forall]
  change IsClosed ((Prod.fst ⁻¹' closure (Set.range (distances X))) ∩
    ⋂ k, {state : Stream × Stream | gap k state.1 * state.2 k = 1})
  exact (isClosed_closure.preimage continuous_fst).inter (isClosed_iInter fun k =>
    isClosed_eq (((gap_continuous k).comp continuous_fst).mul
      ((continuous_apply k).comp continuous_snd)) continuous_const)

theorem graph_range [CompleteSpace X] : Set.range (graph X) = closedCarrier X := by
  ext state
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨subset_closure ⟨x, rfl⟩, fun k => ?_⟩
    exact mul_inv_cancel₀ (ne_of_gt ((gap_pos_iff k _).mp (distances_small X x k)))
  · rintro ⟨inClosure, equations⟩
    have nonzero (k : ℕ) : gap k state.1 ≠ 0 := by
      intro zero
      have impossible := equations k
      rw [zero, zero_mul] at impossible
      exact zero_ne_one impossible
    have small (k : ℕ) : state.1 ∈ smallCoordinate k :=
      (gap_pos_iff k _).mpr (lt_of_le_of_ne infDist_nonneg (Ne.symm (nonzero k)))
    obtain ⟨x, recovered⟩ := range_of_closure_small X inClosure small
    refine ⟨x, Prod.ext recovered ?_⟩
    funext k
    change (gap k (distances X x))⁻¹ = state.2 k
    rw [recovered]
    apply mul_left_cancel₀ (nonzero k)
    rw [mul_inv_cancel₀ (nonzero k)]
    exact (equations k).symm

theorem graph_isClosedEmbedding [CompleteSpace X] : IsClosedEmbedding (graph X) := by
  have continuous : Continuous (graph X) := (distances_continuous X).prodMk (guard_continuous X)
  have embedding : IsEmbedding (graph X) :=
    .of_comp continuous continuous_fst (distances_isEmbedding X)
  exact ⟨embedding, graph_range X ▸ closedCarrier_isClosed X⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding
