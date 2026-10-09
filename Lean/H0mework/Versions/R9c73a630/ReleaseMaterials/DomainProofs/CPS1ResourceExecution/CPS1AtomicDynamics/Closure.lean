import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Facts
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Actual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1AtomicDynamics.Body
noncomputable section

theorem row_at_source (nodes : List Node)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (node : Node) (member : node ∈ nodes) :
    row? (nodes.map (fun node => (node.particle.address,node.row))) node.particle.address = some node.row := by
  induction nodes with
  | nil => cases member
  | cons head rest ih =>
    have partition := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with first | tail
    · subst node
      simp [row?]
    · have different : head.particle.address ≠ node.particle.address := by
        intro same
        apply partition.1
        exact List.mem_map.mpr ⟨node,tail,same.symm⟩
      simpa [row?,different] using
        ih partition.2 tail

theorem gather_exact (particles : List Charged.Particle) (nodes : List Node)
    (same : nodes.map Node.particle = particles)
    (rows : List (Charged.Address × Row))
    (reported : ∀ node ∈ nodes, row? rows node.particle.address = some node.row)
    (positive : ∀ node ∈ nodes, 0 < node.row.inertia) :
    gather particles rows = .ok nodes := by
  subst particles
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
    have known := reported head List.mem_cons_self
    have mass := positive head List.mem_cons_self
    have rest := ih
      (fun node member => reported node (List.mem_cons_of_mem _ member))
      (fun node member => positive node (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,gather_cons,known,if_neg (not_le_of_gt mass),rest]

theorem pulse_whole_carrier (frame : CPS1Recycling.Frame) (state next : State frame)
    (dt : ℝ) (pulse : Pulse) (paid : pulse? frame state dt = .ok (next,pulse)) :
    graph frame next = graph frame state ∧
    pulse.before.map Node.particle = particles frame state ∧
    pulse.after.map Node.particle = particles frame next ∧
    gather (particles frame next) next.rows = .ok pulse.after := by
  unfold pulse? at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  rename_i nodes gathered
  split at paid <;> try contradiction
  dsimp only at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  have same := Except.ok.inj paid
  cases same
  have original := gather_source _ _ _ gathered
  have addresses := gather_unique frame state nodes gathered
  have projected : (nodes.map (fun node => kick node nodes dt)).map Node.particle = nodes.map Node.particle := by
    simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun node _ => (kick_source node nodes dt).1)
  have unique : ((nodes.map (fun node => kick node nodes dt)).map (fun node => node.particle.address)).Nodup := by
    simpa only [List.map_map,Function.comp_def,kick] using addresses
  refine ⟨rfl,original.1,projected.trans original.1,?_⟩
  apply gather_exact _ _ (projected.trans original.1)
  · intro node member
    exact row_at_source _ unique node member
  · intro node member
    rcases List.mem_map.mp member with ⟨old,present,same⟩
    subst node
    exact (original.2 old present).1

end
end CPS1AtomicDynamics.Body
