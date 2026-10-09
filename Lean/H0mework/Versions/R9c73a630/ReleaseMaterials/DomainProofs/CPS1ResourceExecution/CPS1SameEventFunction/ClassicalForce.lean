import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalMeasurement

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics
variable {frame : CPS1Recycling.Frame}

-- This is the full source field, with a source-labelled partition. Numeric
-- slots are global, so the self exclusion cannot erase a cross-material pair.
def chainNodes {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) : List Body.Node :=
  nodes.filter (fun node => !(isAmmoniaNode source node))

theorem source_force_partition {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (node : Body.Node) (nodes : List Body.Node) :
    Body.force node nodes = Body.force node (chainNodes source nodes)+
      Body.force node (ammoniaNodes source nodes) := by
  induction nodes with
  | nil => simp [Body.force,chainNodes,ammoniaNodes]
  | cons head rest ih =>
    cases selected : isAmmoniaNode source head <;>
      simp only [Body.force,List.map_cons,List.sum_cons,chainNodes,ammoniaNodes,
        List.filter_cons,selected,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_false,if_true] at *
    all_goals rw [ih]; abel

theorem chain_force_whole {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) (node : Body.Node) :
    chainForce source nodes node = Body.force node (chainNodes source nodes) := by
  rw [chainForce,source_force_partition]
  abel

theorem pair_force_negative (charge : ℝ) (positive : 0 < charge) (other : Body.Node)
    (signedPosition : 0 < (other.particle.charge : ℝ)*other.row.position (0 : Fin 3)) :
    Coulomb.pairForce charge (other.particle.charge : ℝ) 0 other.row.position (0 : Fin 3) < 0 := by
  have position : other.row.position ≠ 0 := by
    intro zero
    simp only [zero,PiLp.zero_apply,mul_zero,lt_self_iff_false] at signedPosition
  have denominator : 0 < ‖other.row.position‖^3 := pow_pos (norm_pos_iff.mpr position) _
  have numerator : -(charge*((other.particle.charge : ℝ)*other.row.position (0 : Fin 3))) < 0 :=
    neg_neg_of_pos (mul_pos positive signedPosition)
  have paid := div_neg_of_neg_of_pos numerator denominator
  have rearranged : -(charge*((other.particle.charge : ℝ)*other.row.position (0 : Fin 3))) /
      ‖other.row.position‖^3 = charge * (other.particle.charge : ℝ) / ‖other.row.position‖^3 *
        -(other.row.position (0 : Fin 3)) := by ring
  rw [rearranged] at paid
  simpa only [Coulomb.pairForce,zero_sub,norm_neg,PiLp.smul_apply,PiLp.neg_apply,
    smul_eq_mul] using! paid

private theorem force_component (node : Body.Node) (nodes : List Body.Node) :
    Body.force node nodes (0 : Fin 3) =
      (nodes.map (fun other => if other.particle.address = node.particle.address then 0 else
        Coulomb.pairForce (node.particle.charge : ℝ) (other.particle.charge : ℝ)
          node.row.position other.row.position (0 : Fin 3))).sum := by
  induction nodes with
  | nil => rfl
  | cons first rest ih =>
    simp only [Body.force,List.map_cons,List.sum_cons,PiLp.add_apply] at *
    rw [ih]
    split <;> rfl

private theorem sum_nonpositive (values : List ℝ) (nonpositive : ∀ value ∈ values, value ≤ 0) : values.sum ≤ 0 := by
  induction values with
  | nil => exact le_rfl
  | cons value rest ih =>
    exact add_nonpos (nonpositive value List.mem_cons_self)
      (ih (fun other held => nonpositive other (List.mem_cons_of_mem _ held)))

private theorem sum_negative (values : List ℝ) (nonpositive : ∀ value ∈ values, value ≤ 0)
    (negative : ∃ value ∈ values, value < 0) : values.sum < 0 := by
  induction values with
  | nil => obtain ⟨value,held,_⟩ := negative; cases held
  | cons value rest ih =>
    obtain ⟨other,held,strict⟩ := negative
    rcases List.mem_cons.mp held with same | later
    · subst other
      exact add_neg_of_neg_of_nonpos strict
        (sum_nonpositive rest (fun other held => nonpositive other (List.mem_cons_of_mem _ held)))
    · exact add_neg_of_nonpos_of_neg (nonpositive value List.mem_cons_self)
        (ih (fun other held => nonpositive other (List.mem_cons_of_mem _ held)) ⟨other,later,strict⟩)

theorem whole_source_force_negative (target : Body.Node) (nodes : List Body.Node)
    (positive : 0 < (target.particle.charge : ℝ)) (atOrigin : target.row.position = 0)
    (signed : ∀ other ∈ nodes, other.particle.address ≠ target.particle.address →
      0 < (other.particle.charge : ℝ)*other.row.position (0 : Fin 3))
    (hasSource : ∃ other ∈ nodes, other.particle.address ≠ target.particle.address) :
    Body.force target nodes (0 : Fin 3) < 0 := by
  rw [force_component]
  apply sum_negative
  · intro value held
    rcases List.mem_map.mp held with ⟨other,present,rfl⟩
    split
    · exact le_rfl
    · rename_i different
      rw [atOrigin]
      exact (pair_force_negative _ positive other (signed other present different)).le
  · rcases hasSource with ⟨other,present,different⟩
    refine ⟨_,List.mem_map_of_mem present,?_⟩
    rw [if_neg different,atOrigin]
    exact pair_force_negative _ positive other (signed other present different)

end
end CPS1SameEventFunction.Classical
