import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.ElectronicWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Account

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def jointHamiltonian (phase : Phase) (t reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) : ℝ :=
  energy Pointer.baselineHamiltonian resource+Extract.Port.kinetic reserve+
    hamiltonian phase t r p+FiniteActuation.electronicRate phase t*referenceElectronicEnergy rho+
      (translationEnergy rho phase t+electronicControlEnergy phase t)

theorem joint_phase_account (phase : Phase) (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    jointHamiltonian phase t (receiver phase t) (position phase t) (momentum phase t)
      (FiniteContinuation.gammaPath input phase t) (FiniteContinuation.quantumPath input phase t)=
    Live.baselineEnergy input.body.resource.quantum+input.body.resource.momentum+
      nuclearKinetic (FiniteContinuation.momentum input)+sourcePotential := by
  have stock : 0 < receiver phase t := FiniteContinuation.receiver_positive input input_admissible phase t lo hi
  rw [jointHamiltonian,FiniteContinuation.quantum_energy,Extract.Port.kinetic,abs_of_pos stock,
    FiniteContinuation.gamma_centered_energy input input_admissible,mul_zero,add_zero,
    transport_energy_on_fixed_state,add_zero]
  linarith only [receiver_body_account phase t]

theorem joint_clock_partial (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time => jointHamiltonian phase time (receiver phase t) (position phase t) (momentum phase t)
      (FiniteContinuation.gammaPath input phase t) (FiniteContinuation.quantumPath input phase t))
        (-receiverForce phase t) t := by
  simp only [jointHamiltonian,FiniteContinuation.gamma_centered_energy input input_admissible,
    mul_zero,add_zero,transport_energy_on_fixed_state]
  exact (clock_partial phase t).const_add _

theorem joint_receiver_partial (phase : Phase) (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    HasDerivAt (fun reserve => jointHamiltonian phase t reserve (position phase t) (momentum phase t)
      (FiniteContinuation.gammaPath input phase t) (FiniteContinuation.quantumPath input phase t))
        1 (receiver phase t) := by
  unfold jointHamiltonian Extract.Port.kinetic
  exact ((((hasDerivAt_abs_pos (FiniteContinuation.receiver_positive input input_admissible phase t lo hi)).const_add _).add_const _).add_const _).add_const _

theorem joint_force_partial (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointHamiltonian phase t (receiver phase t)
      (Function.update (position phase t) i (position phase t i+h)) (momentum phase t)
      (FiniteContinuation.gammaPath input phase t) (FiniteContinuation.quantumPath input phase t))
        (-force phase t i) 0 := by
  unfold jointHamiltonian
  exact (((position_partial phase t i).const_add _).add_const _).add_const _

theorem joint_velocity_partial (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointHamiltonian phase t (receiver phase t) (position phase t)
      (Function.update (momentum phase t) i (momentum phase t i+h))
      (FiniteContinuation.gammaPath input phase t) (FiniteContinuation.quantumPath input phase t))
        (velocity phase t i) 0 := by
  unfold jointHamiltonian
  exact (((momentum_partial phase t i).const_add _).add_const _).add_const _

theorem complete_joint_control (phase : Phase) (t reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) :
    jointHamiltonian phase t reserve r p rho resource=
      energy Pointer.baselineHamiltonian resource+Extract.Port.kinetic reserve+
        nuclearKinetic (p-vectorControl phase t)+sourcePotential-
        (∑ i, force phase t i*(r i-position phase t i))+scalarControl phase t+
        FiniteActuation.electronicRate phase t*referenceElectronicEnergy rho+
        travelRate phase t*movingTranslationMomentum rho phase t+electronicControlEnergy phase t := by
  rw [jointHamiltonian,complete_control_energy,translationEnergy]
  ring

theorem joint_hamiltonian_junctions (reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) :
    jointHamiltonian .enter duration reserve r p rho resource=jointHamiltonian .drive 0 reserve r p rho resource ∧
    jointHamiltonian .drive duration reserve r p rho resource=jointHamiltonian .leave 0 reserve r p rho resource := by
  rcases FiniteActuation.ramp_endpoints with ⟨_,_,_,onEnd,_,_,offStart,_⟩
  simp only [jointHamiltonian,FiniteActuation.electronicRate,onEnd,offStart,
    translationEnergy,electronicControlEnergy,travelRate,shiftRate,
    FiniteActuation.progress_rate_endpoints.1,FiniteActuation.progress_rate_endpoints.2,
    mul_zero,zero_mul,neg_zero,add_zero]
  rw [(hamiltonian_junctions r p).1,(hamiltonian_junctions r p).2]
  exact ⟨rfl,rfl⟩

theorem resource_quantum_equation (phase : Phase) (t : ℝ) :
    type_of% (FiniteContinuation.quantum_equation input phase t) :=
  FiniteContinuation.quantum_equation input phase t

theorem resource_quantum_integral (phase : Phase) :
    type_of% (FiniteContinuation.quantum_integral input phase) :=
  FiniteContinuation.quantum_integral input phase

theorem full_state_junctions :
    type_of% position_junctions ∧ type_of% (FiniteContinuation.state_junctions input) ∧
      type_of% moving_gamma_junctions :=
  ⟨position_junctions,FiniteContinuation.state_junctions input,moving_gamma_junctions⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
