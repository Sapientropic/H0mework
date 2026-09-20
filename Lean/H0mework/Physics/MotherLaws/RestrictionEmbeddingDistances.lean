import H0mework.Physics.MotherLaws.StreamScalar
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding

open Set Filter Topology TopologicalSpace Metric
open scoped Topology
open MotherStreamLaws

noncomputable section

variable (X : Type*) [MetricSpace X] [SeparableSpace X] [Nonempty X]

def distances (x : X) : Stream := fun n => dist x (denseSeq X n)

theorem distances_continuous : Continuous (distances X) :=
  continuous_pi fun _ => continuous_id.dist continuous_const

theorem distances_reflects_tendsto {A : Type*} {l : Filter A} {u : A → X} {x : X}
    (converges : Tendsto (fun a => distances X (u a)) l (𝓝 (distances X x))) :
    Tendsto u l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  obtain ⟨n, near⟩ := (denseRange_denseSeq X).exists_dist_lt x (by linarith : 0 < ε / 4)
  have coordinate : Tendsto (fun a => dist (u a) (denseSeq X n)) l
      (𝓝 (dist x (denseSeq X n))) :=
    (continuous_apply n).tendsto (distances X x) |>.comp converges
  have eventual : ∀ᶠ a in l, dist (u a) (denseSeq X n) < ε / 2 :=
    coordinate (gt_mem_nhds (by linarith))
  filter_upwards [eventual] with a ha
  calc
    dist (u a) x ≤ dist (u a) (denseSeq X n) + dist (denseSeq X n) x := dist_triangle _ _ _
    _ < ε := by rw [dist_comm (denseSeq X n) x]; linarith

theorem distances_isEmbedding : IsEmbedding (distances X) := by
  have inducing : IsInducing (distances X) := isInducing_iff_nhds.mpr fun x => by
    apply le_antisymm
    · exact (distances_continuous X).continuousAt.le_comap
    · exact distances_reflects_tendsto X tendsto_comap
  exact ⟨inducing, inducing.injective⟩

def smallCoordinate (k : ℕ) : Set Stream := {y | ∃ n, y n < 1 / (k + 1 : ℝ)}

theorem distances_small (x : X) (k : ℕ) : distances X x ∈ smallCoordinate k := by
  exact (denseRange_denseSeq X).exists_dist_lt x (by positivity)

theorem range_of_closure_small [CompleteSpace X] {y : Stream}
    (closed : y ∈ closure (Set.range (distances X)))
    (small : ∀ k, y ∈ smallCoordinate k) : y ∈ Set.range (distances X) := by
  obtain ⟨values, member, converges⟩ := mem_closure_iff_seq_limit.mp closed
  choose sequence represented using member
  have presented : Tendsto (fun n => distances X (sequence n)) atTop (𝓝 y) := by
    simpa only [represented] using converges
  have cauchy : CauchySeq sequence := Metric.cauchySeq_iff.mpr fun ε positive => by
    obtain ⟨k, scale⟩ := exists_nat_one_div_lt (by linarith : 0 < ε / 4)
    obtain ⟨n, near⟩ := small k
    have coordinate : Tendsto (fun j => dist (sequence j) (denseSeq X n)) atTop (𝓝 (y n)) :=
      (continuous_apply n).tendsto y |>.comp presented
    have eventual : ∀ᶠ j in atTop, dist (sequence j) (denseSeq X n) < ε / 2 :=
      coordinate (gt_mem_nhds (by linarith))
    obtain ⟨N, bound⟩ := eventually_atTop.mp eventual
    refine ⟨N, fun a ha b hb => ?_⟩
    calc
      dist (sequence a) (sequence b) ≤
          dist (sequence a) (denseSeq X n) + dist (denseSeq X n) (sequence b) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm (denseSeq X n) (sequence b)]; linarith [bound a ha, bound b hb]
  obtain ⟨x, limit⟩ := cauchySeq_tendsto_of_complete cauchy
  exact ⟨x, tendsto_nhds_unique ((distances_continuous X).tendsto x |>.comp limit) presented⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding
