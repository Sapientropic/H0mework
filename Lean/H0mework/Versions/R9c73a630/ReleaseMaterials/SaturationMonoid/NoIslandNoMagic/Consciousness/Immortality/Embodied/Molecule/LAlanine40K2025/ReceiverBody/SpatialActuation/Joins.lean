import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Hamiltonian

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
noncomputable section

theorem velocity_junctions : velocity .enter duration=velocity .drive 0 ∧
    velocity .drive duration=velocity .leave 0 := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,onEnd,_,_,offStart,_⟩
  have old : FiniteContinuation.velocity input .enter duration=FiniteContinuation.velocity input .drive 0 ∧
      FiniteContinuation.velocity input .drive duration=FiniteContinuation.velocity input .leave 0 := by
    simp only [FiniteContinuation.velocity,onEnd,offStart,zero_mul,zero_div]
    trivial
  exact ⟨by rw [velocity,velocity,old.1,shift_junctions.2.2.1],
    by rw [velocity,velocity,old.2,shift_junctions.2.2.2]⟩

theorem force_junctions : force .enter duration=force .drive 0 ∧
    force .drive duration=force .leave 0 := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,onEnd,_,_,offStart,_⟩
  constructor <;> funext i <;>
    simp only [force,FiniteContinuation.nuclearForce,FiniteContinuation.pulseForce,onEnd,offStart,
    FiniteActuation.progress_rate_endpoints.1,FiniteActuation.progress_rate_endpoints.2,mul_zero,zero_mul]

theorem hamiltonian_junctions (r p : Configuration) :
    hamiltonian .enter duration r p=hamiltonian .drive 0 r p ∧
    hamiltonian .drive duration r p=hamiltonian .leave 0 r p := by
  rcases FiniteContinuation.state_junctions input with ⟨_,_,pa,pb,ra,rb,_⟩
  unfold hamiltonian bodyEnergy receiver momentum
  rw [pa,pb,ra,rb,velocity_junctions.1,velocity_junctions.2,
    force_junctions.1,force_junctions.2,position_junctions.1,position_junctions.2]
  exact ⟨rfl,rfl⟩

theorem source_controls : vectorControl .enter 0=0 ∧ scalarControl .enter 0=0 := by
  rcases FiniteActuation.ramp_endpoints with ⟨onStart,_,onRate,_,_,_,_,_⟩
  have v (i : Coordinate) : velocity .enter 0 i=FiniteContinuation.momentum input i/mass i := by
    simp only [velocity,FiniteContinuation.velocity,shiftRate,Pi.add_apply,onStart,onRate,
      FiniteActuation.ramp_momentum_zero,one_mul,add_zero]
  have p : momentum .enter 0=FiniteContinuation.momentum input := by
    simp only [momentum,FiniteContinuation.nuclearMomentum,onStart,FiniteActuation.ramp_momentum_zero]
  have mv : (fun i => mass i*velocity .enter 0 i)=FiniteContinuation.momentum input := by
    funext i
    rw [v]
    exact mul_div_cancel₀ _ (ne_of_gt (mass_positive i))
  constructor
  · funext i
    simp only [vectorControl,p,congrFun mv i,sub_self,Pi.zero_apply]
  · rw [scalarControl,mv]
    unfold bodyEnergy receiver FiniteContinuation.receiver
    ring

theorem target_controls : vectorControl .leave duration=0 ∧ scalarControl .leave duration=0 := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,_,_,offEnd,_,offRate⟩
  have v (i : Coordinate) : velocity .leave duration i=FiniteContinuation.pulseMomentum input 1 i/mass i := by
    simp only [velocity,FiniteContinuation.velocity,shiftRate,Pi.add_apply,offEnd,offRate,
      FiniteActuation.ramp_momentum_zero,one_mul,add_zero]
  have p : momentum .leave duration=FiniteContinuation.pulseMomentum input 1 := by
    simp only [momentum,FiniteContinuation.nuclearMomentum,offEnd,FiniteActuation.ramp_momentum_zero]
  have mv : (fun i => mass i*velocity .leave duration i)=FiniteContinuation.pulseMomentum input 1 := by
    funext i
    rw [v]
    exact mul_div_cancel₀ _ (ne_of_gt (mass_positive i))
  constructor
  · funext i
    simp only [vectorControl,p,congrFun mv i,sub_self,Pi.zero_apply]
  · rw [scalarControl,mv]
    unfold bodyEnergy receiver FiniteContinuation.receiver FiniteContinuation.pulseReceiver
    ring

def targetPotentialGerm (r : Configuration) : ℝ :=
  sourcePotential-∑ i, sourceForce i*(r i-(sourcePosition i+displacement i))

theorem source_hamiltonian (r p : Configuration) :
    hamiltonian .enter 0 r p=baselineHamiltonian r p := by
  have force0 : force .enter 0=sourceForce := by
    simp only [force,FiniteContinuation.nuclearForce,FiniteActuation.ramp_endpoints.2.2.1,one_mul]
  have position0 : position .enter 0=sourcePosition := by
    simp only [position,FiniteContinuation.nuclearPosition,FiniteActuation.ramp_endpoints.1,
      FiniteActuation.ramp_position_zero,shift]
    exact add_zero _
  rw [complete_control_energy,source_controls.1,source_controls.2,sub_zero,add_zero,force0,position0]
  unfold baselineHamiltonian sourcePotentialGerm
  ring

theorem target_hamiltonian (r p : Configuration) :
    hamiltonian .leave duration r p=nuclearKinetic p+targetPotentialGerm r := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,_,_,offEnd,_,offRate⟩
  have force1 : force .leave duration=sourceForce := by
    simp only [force,FiniteContinuation.nuclearForce,offRate,one_mul]
  have position1 : position .leave duration=fun i => sourcePosition i+displacement i := by
    simp only [position,FiniteContinuation.nuclearPosition,offEnd,FiniteActuation.ramp_position_zero,shift]
    rfl
  rw [complete_control_energy,target_controls.1,target_controls.2,sub_zero,add_zero,force1,position1]
  unfold targetPotentialGerm
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
