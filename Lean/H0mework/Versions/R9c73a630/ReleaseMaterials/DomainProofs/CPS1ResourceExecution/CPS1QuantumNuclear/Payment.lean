import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Pulse

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

theorem currentPrice_source (state : CPS1ElectronicSource.State frame) (reserve : ℝ) :
    (currentPrice state reserve).geometry.nodes = state.geometry.nodes ∧
      (currentPrice state reserve).geometry.originJoint.originBody = state.geometry.originJoint.originBody ∧
      (currentPrice state reserve).geometry.originJoint.components = state.geometry.originJoint.components ∧
      (currentPrice state reserve).geometry.originJoint.rows = state.geometry.originJoint.rows ∧
      (currentPrice state reserve).geometry.originJoint.reserve = reserve ∧
      (currentPrice state reserve).reserve = reserve := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem pulse_paid (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    0 ≤ next.1.reserve ∧ next.1.energy+next.1.reserve = state.energy+state.reserve := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i affordable
  constructor
  · exact sub_nonneg.mpr (not_lt.mp affordable)
  · rw [currentPrice_energy]
    change _ + (state.reserve - (_ - state.energy)) = state.energy+state.reserve
    ring

theorem pulse_source (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    next.1.geometry.originJoint.originBody = state.geometry.originJoint.originBody ∧
      next.1.geometry.originJoint.components = state.geometry.originJoint.components ∧
      next.1.geometry.originJoint.nextOccurrence = state.geometry.originJoint.nextOccurrence ∧
      CPS1EnzymeBath.Joint.particles frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint ∧
      CPS1EnzymeBath.Joint.charge frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.charge frame state.geometry.originJoint ∧
      next.1.geometry.originJoint.reserve = next.1.reserve := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem pulse_good (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next)
    (good : CPS1ElectronicEvolution.Consumer.Good state) :
    CPS1ElectronicEvolution.Consumer.Good next.1 := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact (CPS1ElectronicEvolution.occupied_gram _
    (CPS1ElectronicSource.source_hamiltonian_hermitian _) _ _).trans good

theorem pulse_grounded (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint)
      state.geometry.originJoint.rows = .ok state.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready state.geometry.nodes := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  rename_i nodes gathered
  split at actual <;> try cases actual
  rename_i consistent
  split at actual <;> try cases actual
  rename_i ready
  have same : nodes = state.geometry.nodes := not_ne_iff.mp consistent
  exact ⟨by simpa only [same] using gathered,by simpa only [same] using not_not.mp ready⟩

theorem current_particles_unique (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    (state.geometry.nodes.map (fun node => node.particle.address)).Nodup := by
  classical
  have grounded := (pulse_grounded state time next actual).1
  have same := (CPS1AtomicDynamics.Body.gather_source _ _ _ grounded).1
  have unique := CPS1AtomicDynamics.Charged.particles_unique
    (CPS1EnzymeBath.Joint.descriptorGraph frame state.geometry.originJoint)
  have addresses := congrArg (List.map CPS1AtomicDynamics.Charged.Particle.address) same
  change ((CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint).map CPS1AtomicDynamics.Charged.Particle.address).Nodup at unique
  rw [← addresses] at unique
  simpa only [List.map_map,Function.comp_def] using unique

theorem actual_source_force (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next)
    (direction : CPS1AtomicDynamics.Charged.Address → CPS1AtomicDynamics.Body.Point) :
    spatialEnergyAt state Geometry.nucleusPosition = state.energy ∧
      HasDerivAt (fun duration : ℝ => spatialEnergyAt state (fun nucleus =>
        Geometry.nucleusPosition nucleus+duration • (fun axis => direction nucleus.particle.address axis)))
        (-(state.geometry.nuclei.map (fun nucleus =>
          inner ℝ (nuclearForce state nucleus) (direction nucleus.particle.address))).sum) 0 := by
  classical
  have unique := current_particles_unique state time next actual
  have pair := List.pairwise_map.mp unique
  have nuclearUnique : (state.geometry.nuclei.map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr (pair.filter _)
  have ready := (pulse_grounded state time next actual).2
  have nuclearReady : CPS1AtomicDynamics.Body.ready state.geometry.nuclei := ready.filter _
  exact ⟨original_total_energy state,source_nuclear_energy_line state nuclearUnique nuclearReady direction⟩

theorem pulse_atoms_and_bonds (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    CPS1EnzymeBath.Joint.atoms frame next.1.geometry.originJoint =
      CPS1EnzymeBath.Joint.atoms frame state.geometry.originJoint ∧
      CPS1EnzymeBath.Joint.bonds frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.bonds frame state.geometry.originJoint := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  exact ⟨rfl,rfl⟩

end
end CPS1QuantumNuclear
