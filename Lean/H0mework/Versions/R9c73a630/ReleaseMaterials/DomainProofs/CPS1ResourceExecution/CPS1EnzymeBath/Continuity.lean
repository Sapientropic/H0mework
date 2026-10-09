import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Bonds
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Dynamics

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Joint
noncomputable section
open CPS1AtomicDynamics

def ComponentsValid (frame : CPS1Recycling.Frame) (state : State frame) : Prop :=
  state.components.map Component.occurrence = List.range state.nextOccurrence

theorem initial_components (frame : CPS1Recycling.Frame) (body : Body.State frame) :
    ComponentsValid frame (fromBody frame body) := rfl

theorem attach_components (frame : CPS1Recycling.Frame) (state : State frame)
    (valid : ComponentsValid frame state) (kind : Primary.TemplateKind) :
    ComponentsValid frame (attach frame state kind) := by
  simp only [ComponentsValid,attach,List.map_append,List.map_cons,List.map_nil]
  rw [valid,List.range_succ]

theorem unique_components (frame : CPS1Recycling.Frame) (state : State frame)
    (valid : ComponentsValid frame state) : (state.components.map Component.occurrence).Nodup := by
  rw [valid]
  exact List.nodup_range

private theorem zipIdx_append {A : Type} (before after : List A) (offset : Nat) :
    (before ++ after).zipIdx offset = before.zipIdx offset ++ after.zipIdx (offset+before.length) := by
  induction before generalizing offset with
  | nil => simp
  | cons head rest ih =>
    simp only [List.cons_append,List.zipIdx_cons,ih,List.cons_append,List.length_cons]
    have arithmetic : offset+1+rest.length = offset+(rest.length+1) := by omega
    rw [arithmetic]

theorem append_atoms (frame : CPS1Recycling.Frame) (state : State frame) (kind : Primary.TemplateKind) :
    atoms frame (attach frame state kind) = atoms frame state ++
      (Primary.template kind).atoms.map (bathAtom ⟨state.nextOccurrence,kind⟩) := by
  simp only [atoms,attach,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [List.append_assoc]

theorem append_particles (frame : CPS1Recycling.Frame) (state : State frame) (kind : Primary.TemplateKind) :
    particles frame (attach frame state kind) = particles frame state ++
      (((Primary.template kind).atoms.map (fun atom => (bathAtom ⟨state.nextOccurrence,kind⟩ atom).descriptor)).zipIdx
        ((atoms frame state).length)).flatMap Charged.atomParticles := by
  simp only [particles,descriptorGraph,append_atoms,List.map_append,Charged.particles]
  rw [zipIdx_append,List.flatMap_append]
  simp only [zero_add,List.length_map,List.map_map,Function.comp_def]

theorem old_particle_retained (frame : CPS1Recycling.Frame) (state : State frame) (kind : Primary.TemplateKind)
    (particle : Charged.Particle) (member : particle ∈ particles frame state) :
    particle ∈ particles frame (attach frame state kind) := by
  rw [append_particles]
  exact List.mem_append_left _ member

theorem pulse_whole (frame : CPS1Recycling.Frame) (state next : State frame) (dt : ℝ)
    (pulse : Body.Pulse) (paid : pulse? frame state dt = .ok (next,pulse)) :
    atoms frame next = atoms frame state ∧ bonds frame next = bonds frame state ∧
    pulse.after.map Body.Node.particle = particles frame next ∧
    Body.gather (particles frame next) next.rows = .ok pulse.after := by
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
  have source := Body.gather_source _ _ _ gathered
  have projected : (nodes.map (fun node => Body.kick node nodes dt)).map Body.Node.particle = nodes.map Body.Node.particle := by
    simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun node _ => (Body.kick_source node nodes dt).1)
  have addresses := congrArg (List.map Charged.Particle.address) source.1
  have initialUnique : (nodes.map (fun node => node.particle.address)).Nodup := by
    have known := particle_unique frame state
    rw [← addresses] at known
    simpa only [List.map_map,Function.comp_def] using known
  have unique : ((nodes.map (fun node => Body.kick node nodes dt)).map (fun node => node.particle.address)).Nodup := by
    simpa only [List.map_map,Function.comp_def,Body.kick] using initialUnique
  refine ⟨rfl,rfl,projected.trans source.1,?_⟩
  apply Body.gather_exact _ _ (projected.trans source.1)
  · intro node member
    exact Body.row_at_source _ unique node member
  · intro node member
    rcases List.mem_map.mp member with ⟨old,present,same⟩
    subst node
    exact (source.2 old present).1

end
end CPS1EnzymeBath.Joint
