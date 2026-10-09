import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Unique

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1AtomicDynamics

def registrationPoint (index : Nat) : Body.Point :=
  WithLp.toLp 2 (fun axis : Fin 3 => if axis = 0 then (index : ℝ) else 0)

def registrationRow (index : Nat) : Body.Row := ⟨registrationPoint index,0,1⟩

def registrationNodes (particles : List Charged.Particle) : List Body.Node :=
  particles.zipIdx.map (fun entry => ⟨entry.1,registrationRow entry.2⟩)

def registrationRows (particles : List Charged.Particle) : List (Charged.Address × Body.Row) :=
  (registrationNodes particles).map (fun node => (node.particle.address,node.row))

theorem registration_point_injective : Function.Injective registrationPoint := by
  intro first second same
  have coordinate := congrArg (fun point : Body.Point => point 0) same
  simp only [registrationPoint,WithLp.ofLp_toLp,ite_true] at coordinate
  exact_mod_cast coordinate

theorem registration_nodes_particles (particles : List Charged.Particle) :
    (registrationNodes particles).map Body.Node.particle = particles := by
  simp only [registrationNodes,List.map_map,Function.comp_def]
  exact List.zipIdx_map_fst 0 particles

theorem registration_nodes_ready (particles : List Charged.Particle) :
    Body.ready (registrationNodes particles) := by
  have indices : (particles.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have pairwise : particles.zipIdx.Pairwise (fun first second => first.2 ≠ second.2) :=
    List.pairwise_map.mp indices
  apply List.pairwise_map.mpr
  exact pairwise.imp (by
    intro first second different same
    exact different (registration_point_injective same))

theorem registration_nodes_positive (particles : List Charged.Particle) (node : Body.Node)
    (held : node ∈ registrationNodes particles) : 0 < node.row.inertia := by
  obtain ⟨entry,_present,same⟩ := List.mem_map.mp held
  subst node
  change (0 : ℝ) < 1
  norm_num

theorem registration_nodes_unique (particles : List Charged.Particle)
    (unique : (particles.map Charged.Particle.address).Nodup) :
    ((registrationNodes particles).map (fun node => node.particle.address)).Nodup := by
  have actual := congrArg (List.map Charged.Particle.address) (registration_nodes_particles particles)
  simp only [List.map_map,Function.comp_def] at actual
  rw [actual]
  exact unique

theorem registration_rows_actual (particles : List Charged.Particle)
    (unique : (particles.map Charged.Particle.address).Nodup) :
    Body.gather particles (registrationRows particles) = .ok (registrationNodes particles) := by
  apply Body.gather_exact particles (registrationNodes particles) (registration_nodes_particles particles)
  · intro node held
    exact Body.row_at_source _ (registration_nodes_unique particles unique) node held
  · exact registration_nodes_positive particles

def registrationBodyActions (particles : List Charged.Particle) : List CPS1AtomicDynamics.Source.RawAction :=
  (registrationRows particles).map (fun entry => .report entry.1 entry.2)

def registrationBathActions (particles : List Charged.Particle) : List CPS1EnzymeBath.Source.RawAction :=
  (registrationRows particles).map (fun entry => .report entry.1 entry.2)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
