import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Account
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Calibration

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation
noncomputable section

structure WorkReadout where
  receiverBeforeJoule : ℝ
  receiverAfterJoule : ℝ
  bodyBeforeJoule : ℝ
  bodyAfterJoule : ℝ
  debitJoule : ℝ
  elapsedSecond : ℝ

def workOf (current : Material) : WorkReadout :=
  ⟨energyJoule*current.body.resource.momentum,energyJoule*(nextMaterial current).body.resource.momentum,
   energyJoule*(current.body.frame.total : ℝ),energyJoule*((nextMaterial current).body.frame.total : ℝ),
   workJoule current,3*segmentSeconds⟩

theorem work_readout_balance (current : Material) (valid : Admissible current) :
    (workOf current).receiverBeforeJoule-(workOf current).receiverAfterJoule=(workOf current).debitJoule ∧
    (workOf current).bodyAfterJoule-(workOf current).bodyBeforeJoule=(workOf current).debitJoule ∧
    0 < (workOf current).debitJoule ∧ 0 < (workOf current).elapsedSecond := by
  refine ⟨?_,?_,work_positive current valid,?_⟩
  · unfold workOf workJoule
    ring
  · change energyJoule*((nextMaterial current).body.frame.total : ℝ)-energyJoule*(current.body.frame.total : ℝ)=workJoule current
    rw [work_from_body current valid]
    ring
  · change 0 < 3*segmentSeconds
    exact mul_pos (by norm_num) segment_positive

structure CalibratedAction (current : FiniteContinuation.Runtime.State) : Prop where
  parentAction : FiniteContinuation.Runtime.ActualStep current
  source : type_of% source_identity
  unitAction : type_of% calibration_action_commutes
  unitMass : type_of% calibration_mass_commutes
  clockUnit : type_of% original_q_seconds
  mass : type_of% nucleus_mass_positive
  kinetic : type_of% kinetic_from_physical_momenta
  position : type_of% (position_equation_si current.1)
  momentum : type_of% (momentum_equation_si current.1)
  receiver : type_of% (receiver_equation_si current.1)
  gamma : type_of% (gamma_equation_si current.1)
  quantum : type_of% (quantum_equation_si current.1)
  forcePartial : type_of% (joint_force_si current.1)
  velocityPartial : type_of% (joint_velocity_si current.1)
  clockPartial : type_of% (joint_clock_si current.1 current.2)
  receiverPartial : type_of% (joint_receiver_si current.1 current.2)
  completeEnergy : type_of% (complete_physical_hamiltonian current.1)
  phaseEnergy : type_of% (joint_energy_si current.1 current.2)
  joins : type_of% (hamiltonian_junctions_si current.1)
  positive : type_of% (phase_stock_joule current.1 current.2)
  positionIntegral : type_of% (position_integral_si current.1)
  momentumIntegral : type_of% (momentum_integral_si current.1)
  receiverIntegral : type_of% (receiver_integral_si current.1)
  gammaIntegral : type_of% (gamma_integral_si current.1)
  quantumIntegral : type_of% (quantum_integral_si current.1)
  momentumUpdate : type_of% (total_momentum_integral_si current.1 current.2)
  receiverUpdate : type_of% (total_receiver_integral_si current.1 current.2)
  gammaEndpoints : type_of% (gamma_endpoints_si current.1 current.2)
  quantumEndpoints : type_of% (quantum_endpoints_si current.1 current.2)
  gammaResiduals : type_of% (gamma_residual_si current.1 current.2)
  account : type_of% (next_account_si current.1 current.2)
  work : type_of% (work_readout_balance current.1 current.2)
  engineWork : type_of% (work_engine_residual current.1 current.2)
  engineEnergyResidual : type_of% engine_energy_rounding_nonzero
  energyPrecision : type_of% engine_energy_rounding_bound
  lengthPrecision : type_of% engine_length_rounding_bound
  lengthResidual : type_of% length_coordinate_residual

theorem calibratedAction (current : FiniteContinuation.Runtime.State) : CalibratedAction current :=
  ⟨FiniteContinuation.Runtime.actualStep current,source_identity,calibration_action_commutes,
   calibration_mass_commutes,original_q_seconds,nucleus_mass_positive,kinetic_from_physical_momenta,
   position_equation_si current.1,momentum_equation_si current.1,receiver_equation_si current.1,
   gamma_equation_si current.1,quantum_equation_si current.1,joint_force_si current.1,joint_velocity_si current.1,
   joint_clock_si current.1 current.2,joint_receiver_si current.1 current.2,complete_physical_hamiltonian current.1,
   joint_energy_si current.1 current.2,hamiltonian_junctions_si current.1,phase_stock_joule current.1 current.2,
   position_integral_si current.1,momentum_integral_si current.1,receiver_integral_si current.1,
   gamma_integral_si current.1,quantum_integral_si current.1,total_momentum_integral_si current.1 current.2,
   total_receiver_integral_si current.1 current.2,gamma_endpoints_si current.1 current.2,
   quantum_endpoints_si current.1 current.2,gamma_residual_si current.1 current.2,next_account_si current.1 current.2,
   work_readout_balance current.1 current.2,work_engine_residual current.1 current.2,engine_energy_rounding_nonzero,
   engine_energy_rounding_bound,engine_length_rounding_bound,length_coordinate_residual⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
