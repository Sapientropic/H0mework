import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Charged

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1AtomicDynamics.Charged

def Address.slot : Address → Nat
  | .nucleus slot => slot | .electron slot _ => slot

theorem atom_particle_slot (row : CPS1AtomicSource.Graph.Atom × Nat) (particle : Particle)
    (member : particle ∈ atomParticles row) : particle.address.slot = row.2 := by
  rcases List.mem_cons.mp member with first | rest
  · cases first
    rfl
  · rcases List.mem_map.mp rest with ⟨index,_,same⟩
    cases same
    rfl

theorem atom_particles_unique (row : CPS1AtomicSource.Graph.Atom × Nat) :
    ((atomParticles row).map Particle.address).Nodup := by
  simp only [atomParticles,List.map_cons,List.map_map,Function.comp_def]
  apply List.nodup_cons.mpr
  constructor
  · simp
  · apply List.Nodup.map _ List.nodup_range
    intro first second same
    exact (Address.electron.inj same).2

theorem particles_unique (graph : CPS1AtomicSource.Graph.Molecule) :
    ((particles graph).map Particle.address).Nodup := by
  have slots : (graph.atoms.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have rows : graph.atoms.zipIdx.Pairwise (fun first second => first.2 ≠ second.2) :=
    List.pairwise_map.mp slots
  apply List.pairwise_map.mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro row _
    exact List.pairwise_map.mp (atom_particles_unique row)
  · apply rows.imp
    intro first second different a amember b bmember same
    apply different
    have key := congrArg Address.slot same
    rw [atom_particle_slot first a amember,atom_particle_slot second b bmember] at key
    exact key

end CPS1AtomicDynamics.Charged
