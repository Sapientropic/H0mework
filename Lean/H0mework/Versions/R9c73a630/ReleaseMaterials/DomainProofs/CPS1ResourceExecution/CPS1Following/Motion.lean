import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Relocation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

/-- A subordinate inverse for the same source rows. The live caller supplies
its generated field; this theorem chooses neither a force nor an occurrence. -/
theorem moved_gather (state : CPS1ElectronicSource.State frame) (field : Node → BodyPoint) (time : ℝ)
    (gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint)
      state.geometry.originJoint.rows = .ok state.geometry.nodes) :
    CPS1AtomicDynamics.Body.gather
      (CPS1EnzymeBath.Joint.particles frame (CPS1QuantumNuclear.movedJoint state
        (CPS1QuantumNuclear.nextNodes state field time)))
      (CPS1QuantumNuclear.movedJoint state (CPS1QuantumNuclear.nextNodes state field time)).rows =
      .ok (CPS1QuantumNuclear.nextNodes state field time) := by
  have source := CPS1AtomicDynamics.Body.gather_source _ _ _ gathered
  have whole := CPS1QuantumNuclear.moved_particle_rows state field time
  have original : (state.geometry.nodes.map (fun node => node.particle.address)).Nodup := by
    have unique := CPS1AtomicDynamics.Charged.particles_unique
      (CPS1EnzymeBath.Joint.descriptorGraph frame state.geometry.originJoint)
    have addresses := congrArg (List.map CPS1AtomicDynamics.Charged.Particle.address) source.1
    change ((CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint).map
      CPS1AtomicDynamics.Charged.Particle.address).Nodup at unique
    rw [← addresses] at unique
    simpa only [List.map_map,Function.comp_def] using unique
  have aligned : (CPS1QuantumNuclear.nextNodes state field time).map (fun node => node.particle.address) =
      state.geometry.nodes.map (fun node => node.particle.address) := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map CPS1AtomicDynamics.Charged.Particle.address) whole
  have unique : ((CPS1QuantumNuclear.nextNodes state field time).map (fun node => node.particle.address)).Nodup := by
    rw [aligned]
    exact original
  apply CPS1AtomicDynamics.Body.gather_exact _ _ (whole.trans source.1)
  · exact CPS1AtomicDynamics.Body.row_at_source _ unique
  · intro node member
    rcases List.mem_map.mp member with ⟨before,present,same⟩
    subst node
    rw [(CPS1QuantumNuclear.nuclear_whole before (field before) time).2]
    exact (source.2 before present).1

theorem moved_isNucleus (node : Node) (field : BodyPoint) (time : ℝ) :
    isNucleus (CPS1QuantumNuclear.moveNucleus node field time) = isNucleus node := by
  unfold isNucleus
  rw [(CPS1QuantumNuclear.nuclear_whole node field time).1]

theorem moved_nuclei (state : CPS1ElectronicSource.State frame) (field : Node → BodyPoint) (time : ℝ) :
    (CPS1QuantumNuclear.movedState state (CPS1QuantumNuclear.nextNodes state field time)).geometry.nuclei =
      state.geometry.nuclei.map (fun node => CPS1QuantumNuclear.moveNucleus node (field node) time) := by
  simp only [CPS1QuantumNuclear.movedState,CPS1QuantumNuclear.movedGeometry,Geometry.nuclei,
    CPS1QuantumNuclear.nextNodes,List.filter_map,Function.comp_def,moved_isNucleus]

theorem moved_massTotal (state : CPS1ElectronicSource.State frame) (field : Node → BodyPoint) (time : ℝ) :
    massTotal (CPS1QuantumNuclear.movedState state (CPS1QuantumNuclear.nextNodes state field time)) =
      massTotal state := by
  unfold massTotal
  rw [moved_nuclei]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro node _
  exact (CPS1QuantumNuclear.nuclear_whole node (field node) time).2

end
end CPS1Following
