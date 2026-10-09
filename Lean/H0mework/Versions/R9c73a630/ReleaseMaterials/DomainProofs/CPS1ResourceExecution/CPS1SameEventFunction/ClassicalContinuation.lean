import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalDynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.SuccessNeighborhood
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Field

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics Filter
open scoped Topology
variable {frame : CPS1Recycling.Frame}

private theorem kick_zero (node : Body.Node) (nodes : List Body.Node) : Body.kick node nodes 0 = node := by
  simp only [Body.kick,zero_div,zero_pow (by decide : 2 ≠ 0),zero_smul,add_zero]

private theorem position_continuous (node : Body.Node) (nodes : List Body.Node) :
    ContinuousAt (fun time : ℝ => (Body.kick node nodes time).row.position) 0 := by
  exact (continuousAt_const.add ((continuousAt_id.div_const node.row.inertia).smul continuousAt_const)).add
    (((continuousAt_id.pow 2).div_const (2*node.row.inertia)).smul continuousAt_const)

private theorem momentum_continuous (node : Body.Node) (nodes : List Body.Node) :
    ContinuousAt (fun time : ℝ => (Body.kick node nodes time).row.momentum) 0 :=
  continuousAt_const.add (continuousAt_id.smul continuousAt_const)

private theorem list_sum_continuous {A : Type} (items : List A) (f : A → ℝ → ℝ)
    (continuous : ∀ item ∈ items, ContinuousAt (f item) 0) :
    ContinuousAt (fun time => (items.map (fun item => f item time)).sum) 0 := by
  induction items with
  | nil => exact continuousAt_const
  | cons item rest ih =>
    exact (continuous item List.mem_cons_self).add
      (ih (fun later held => continuous later (List.mem_cons_of_mem _ held)))

private theorem moving_potential_continuous (whole selected : List Body.Node) (separated : Body.ready selected) :
    ContinuousAt (fun time : ℝ => Body.potential (selected.map (fun node => Body.kick node whole time))) 0 := by
  induction selected with
  | nil => exact continuousAt_const
  | cons first rest ih =>
    have pairwise := List.pairwise_cons.mp separated
    have head := list_sum_continuous rest
      (fun second time => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        (Body.kick first whole time).row.position (Body.kick second whole time).row.position)
      (fun second held => by
        have relative := (position_continuous first whole).sub (position_continuous second whole)
        have nonzero : ‖(Body.kick first whole 0).row.position-(Body.kick second whole 0).row.position‖ ≠ 0 := by
          rw [kick_zero,kick_zero]
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (pairwise.1 second held))
        exact continuousAt_const.div relative.norm nonzero)
    simpa only [List.map_cons,Body.potential,List.map_map,Function.comp_def] using! head.add (ih pairwise.2)

theorem moving_energy_continuous (nodes : List Body.Node) (separated : Body.ready nodes) :
    ContinuousAt (fun time : ℝ => Body.energy (nodes.map (fun node => Body.kick node nodes time))) 0 := by
  have kinetic := list_sum_continuous nodes
    (fun node time => Coulomb.kinetic node.row.inertia (Body.kick node nodes time).row.momentum)
    (fun node _ => ((momentum_continuous node nodes).norm.pow 2).div_const (2*node.row.inertia))
  simpa only [Body.energy,Body.kinetic,List.map_map,Function.comp_def] using!
    kinetic.add (moving_potential_continuous nodes nodes separated)

theorem source_success_eventually {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (current : Current cursor raw) (ready : Body.ready current.nodes) (positive : 0 < current.reserve)
    (acted : SourceActs current.packet.source current.nodes) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time → ∃ step, nativeStep current time = .ok step := by
  have atZero : (current.nodes.map (fun node => Body.kick node current.nodes 0)) = current.nodes := by
    simp only [kick_zero,List.map_id_fun',id_eq]
  have positions := CPS1PositivePulse.pairwise_positions_eventually current.nodes
    (fun time node => (Body.kick node current.nodes time).row.position)
    (fun node _ => position_continuous node current.nodes)
    (by simpa only [Body.ready,kick_zero] using ready)
  have energy : ContinuousAt (fun time : ℝ =>
      Body.energy (current.nodes.map (fun node => Body.kick node current.nodes time))-current.energy) 0 :=
    (moving_energy_continuous current.nodes ready).sub continuousAt_const
  have differenceZero : Body.energy (current.nodes.map (fun node => Body.kick node current.nodes 0))-current.energy = 0 := by
    rw [atZero]
    exact sub_self _
  have budget := energy.eventually (gt_mem_nhds (by simpa only [differenceZero] using positive))
  filter_upwards [positions,budget] with time separated affordable elapsed
  unfold nativeStep
  simp only [dif_pos elapsed,dif_pos positive.le,dif_pos ready,dif_pos acted]
  have nextReady : Body.ready (current.nodes.map (fun node => Body.kick node current.nodes time)) := by
    simpa only [Body.ready,List.pairwise_map] using separated
  simp only [dif_pos nextReady,dif_pos affordable.le]
  exact ⟨_,rfl⟩

end
end CPS1SameEventFunction.Classical
