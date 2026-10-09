import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Flows

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
noncomputable section

theorem state_junctions (current : Material) :
    nuclearPosition current .enter duration=nuclearPosition current .drive 0 ∧
    nuclearPosition current .drive duration=nuclearPosition current .leave 0 ∧
    nuclearMomentum current .enter duration=nuclearMomentum current .drive 0 ∧
    nuclearMomentum current .drive duration=nuclearMomentum current .leave 0 ∧
    receiver current .enter duration=receiver current .drive 0 ∧
    receiver current .drive duration=receiver current .leave 0 ∧
    gammaPath current .enter duration=gammaPath current .drive 0 ∧
    gammaPath current .drive duration=gammaPath current .leave 0 ∧
    quantumPath current .enter duration=quantumPath current .drive 0 ∧
    quantumPath current .drive duration=quantumPath current .leave 0 := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,b,_,_,e,_,_,_⟩
  simp only [nuclearPosition,nuclearMomentum,receiver,gammaPath,FiniteActuation.electronicTime,b,e,
    FiniteActuation.ramp_position_zero,FiniteActuation.ramp_momentum_zero,
    FiniteActuation.progress_endpoints.1,FiniteActuation.progress_endpoints.2,
    (momentum_endpoints current).1,pulseReceiver,quantum_finish,quantum_start,quantumInput,add_sub_cancel_right]
  trivial

theorem hamiltonian_junctions (current : Material) (reserve : ℝ) (r p : Configuration)
    (rho : Matrix Propagation.Interface.Basis Propagation.Interface.Basis ℂ)
    (resource : Thermal.Recovery.Reservoir.Pointer.PointerJoint) :
    jointHamiltonian current .enter duration reserve r p rho resource=
      jointHamiltonian current .drive 0 reserve r p rho resource ∧
    jointHamiltonian current .drive duration reserve r p rho resource=
      jointHamiltonian current .leave 0 reserve r p rho resource := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,b,_,d,e,_,g,_⟩
  simp only [jointHamiltonian,nuclearEnergy,FiniteActuation.electronicRate,b,d,e,g,zero_mul,add_zero]
  rw [(pulse_junctions current r p).1,(pulse_junctions current r p).2]
  exact ⟨rfl,rfl⟩

theorem source_endpoints (current : Material) (valid : Admissible current) (i : Coordinate) :
    nuclearPosition current .enter 0 i=(current.body.frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum current .enter 0 i=(current.body.frame.momentum i.1 i.2 : ℝ) ∧
    receiver current .enter 0=current.body.resource.momentum ∧
    gammaPath current .enter 0=current.body.realized ∧
    quantumPath current .enter 0=current.body.resource.quantum.joint := by
  rcases FiniteActuation.ramp_endpoints with ⟨a,_,_,_,_,_,_,_⟩
  simp only [nuclearPosition,nuclearMomentum,gammaPath,FiniteActuation.electronicTime,a,
    FiniteActuation.ramp_position_zero,FiniteActuation.ramp_momentum_zero,
    FiniteActuation.electron_flow_zero,quantum_start,quantumInput,receiver]
  refine ⟨(position_at_source current valid i).symm,rfl,?_⟩
  trivial

theorem target_endpoints (current : Material) (valid : Admissible current) (i : Coordinate) :
    nuclearPosition current .leave duration i=((nextMaterial current).body.frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum current .leave duration i=((nextMaterial current).body.frame.momentum i.1 i.2 : ℝ) ∧
    receiver current .leave duration=(nextMaterial current).body.resource.momentum ∧
    gammaPath current .leave duration=(nextMaterial current).body.realized ∧
    quantumPath current .leave duration=(nextMaterial current).body.resource.quantum.joint := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,_,_,f,_,_⟩
  simp only [nuclearPosition,nuclearMomentum,gammaPath,FiniteActuation.electronicTime,f,
    FiniteActuation.ramp_position_zero,FiniteActuation.ramp_momentum_zero,
    FiniteActuation.electron_flow_zero,quantum_finish]
  refine ⟨(position_at_source current valid i).symm,?_,(receiver_endpoints current valid).2,rfl,rfl⟩
  exact congrFun (momentum_endpoints current).2 i

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
