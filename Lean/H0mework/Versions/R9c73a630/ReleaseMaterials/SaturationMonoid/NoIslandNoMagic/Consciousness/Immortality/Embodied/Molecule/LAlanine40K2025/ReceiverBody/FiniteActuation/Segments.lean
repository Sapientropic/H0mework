import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Electronic

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

inductive Phase | enter | drive | leave deriving DecidableEq

def phaseOffset : Phase → ℝ
  | .enter => 0
  | .drive => duration
  | .leave => 2*duration

def electronicTime : Phase → ℝ → ℝ
  | .enter => onTime
  | .drive => fun _ => 0
  | .leave => offTime

def electronicRate : Phase → ℝ → ℝ
  | .enter => onRate
  | .drive => fun _ => 0
  | .leave => offRate

def nuclearPosition : Phase → ℝ → Configuration
  | .enter => fun t => rampPosition initialMomentum (onTime t)
  | .drive => fun _ => sourcePosition
  | .leave => fun t => rampPosition (plateauMomentum 1) (offTime t)

def nuclearMomentum : Phase → ℝ → Configuration
  | .enter => fun t => rampMomentum initialMomentum (onTime t)
  | .drive => fun t => plateauMomentum (progress t)
  | .leave => fun t => rampMomentum (plateauMomentum 1) (offTime t)

def receiver : Phase → ℝ → ℝ
  | .enter => fun _ => initialReceiver
  | .drive => fun t => plateauReceiver (progress t)
  | .leave => fun _ => plateauReceiver 1

def nuclearEnergy : Phase → ℝ → Configuration → Configuration → ℝ
  | .enter => fun t => rampHamiltonian initialMomentum (onTime t) (onRate t)
  | .drive => plateauHamiltonian
  | .leave => fun t => rampHamiltonian (plateauMomentum 1) (offTime t) (offRate t)

def quantumInput : Phase → Live.State
  | .enter => input.joint.body.resource.quantum
  | .drive => Live.loadNext input.joint.body.resource.quantum
  | .leave => Live.loadNext (Live.loadNext input.joint.body.resource.quantum)

def quantumPath (phase : Phase) (t : ℝ) : PointerJoint :=
  conjugation (Pointer.loadPulse t) (quantumInput phase).joint

def gammaPath (phase : Phase) (t : ℝ) : Matrix Basis Basis ℂ :=
  electronFlow input.joint.body.realized (electronicTime phase t)

def jointHamiltonian (phase : Phase) (t reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) : ℝ :=
  energy Pointer.baselineHamiltonian resource+Extract.Port.kinetic reserve+
    nuclearEnergy phase t r p+electronicRate phase t*referenceElectronicEnergy rho

def phaseEnergy (phase : Phase) (t : ℝ) : ℝ :=
  jointHamiltonian phase t (receiver phase t) (nuclearPosition phase t)
    (nuclearMomentum phase t) (gammaPath phase t) (quantumPath phase t)

theorem electronic_time_derivative (phase : Phase) (t : ℝ) :
    HasDerivAt (electronicTime phase) (electronicRate phase t) t := by
  cases phase with
  | enter => exact on_time_derivative t
  | drive => exact hasDerivAt_const t 0
  | leave => exact off_time_derivative t

theorem gamma_equation (phase : Phase) (t : ℝ) :
    HasDerivAt (gammaPath phase)
      (-Complex.I • (electronHamiltonian (electronicRate phase t)*gammaPath phase t-
        gammaPath phase t*electronHamiltonian (electronicRate phase t))) t :=
  electron_equation _ _ _ _ (electronic_time_derivative phase t)

theorem quantum_generated (phase : Phase) (t : ℝ) :
    quantumPath phase t=Extract.Port.bodyFlow Pointer.baselineHamiltonian (quantumInput phase).joint t := by
  rw [quantumPath,conjugation_apply,Pointer.loadPulse_baseline]
  rfl

theorem quantum_equation (phase : Phase) (t : ℝ) :
    HasDerivAt (quantumPath phase)
      (-Complex.I • (Pointer.baselineHamiltonian*quantumPath phase t-
        quantumPath phase t*Pointer.baselineHamiltonian)) t := by
  change HasDerivAt (fun time => quantumPath phase time) _ t
  simp_rw [quantum_generated]
  exact Extract.Port.body_flow_liouville _ _ Pointer.baselineHamiltonian_hermitian t

theorem quantum_start (phase : Phase) : quantumPath phase 0=(quantumInput phase).joint := by
  rw [quantum_generated]
  simp [Extract.Port.bodyFlow,hamiltonianFlow]

theorem quantum_finish (phase : Phase) : quantumPath phase duration=(Live.loadNext (quantumInput phase)).joint :=
  (Live.loadNext_joint (quantumInput phase)).symm

theorem quantum_energy (phase : Phase) (t : ℝ) :
    energy Pointer.baselineHamiltonian (quantumPath phase t)=Live.baselineEnergy input.joint.body.resource.quantum := by
  rw [quantumPath,Extract.Port.Timeline.load_energy_preserved]
  change Live.baselineEnergy (quantumInput phase)=_
  cases phase <;> simp only [quantumInput,Live.loadNext_preserves_baseline]

theorem receiver_positive (phase : Phase) (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    0 < receiver phase t := by
  cases phase with
  | enter => exact initial_receiver_positive
  | drive => exact (half_pos initial_receiver_positive).trans (finite_plateau_stock t lo hi)
  | leave => exact (half_pos initial_receiver_positive).trans (plateau_receiver_positive 1 (by norm_num) (by norm_num))

theorem nuclear_receiver_account (phase : Phase) (t : ℝ) :
    receiver phase t+nuclearEnergy phase t (nuclearPosition phase t) (nuclearMomentum phase t)=
      initialReceiver+initialKinetic+sourcePotential := by
  cases phase with
  | enter =>
      dsimp only [receiver,nuclearEnergy,nuclearPosition,nuclearMomentum]
      rw [ramp_energy]
      change initialReceiver+(initialKinetic+sourcePotential)=_
      ring
  | drive => exact plateau_account t
  | leave =>
      dsimp only [receiver,nuclearEnergy,nuclearPosition,nuclearMomentum]
      rw [ramp_energy,plateauReceiver]
      ring

theorem phase_energy_account (phase : Phase) (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    phaseEnergy phase t=Live.baselineEnergy input.joint.body.resource.quantum+
      initialReceiver+initialKinetic+sourcePotential := by
  rw [phaseEnergy,jointHamiltonian,quantum_energy,Extract.Port.kinetic,
    abs_of_pos (receiver_positive phase t lo hi)]
  have electronic : referenceElectronicEnergy (gammaPath phase t)=0 := electron_centered_energy _
  rw [electronic,mul_zero,add_zero]
  have nuclear := nuclear_receiver_account phase t
  linarith only [nuclear]

theorem physical_clocks (phase : Phase) (t : ℝ) :
    ((input.joint.body.resource.quantum.localClock : ℝ)+phaseOffset phase+t)-
      (input.joint.body.resource.quantum.localClock : ℝ)=phaseOffset phase+t ∧
    ((input.joint.body.bodyClock : ℝ)+phaseOffset phase+t)-(input.joint.body.bodyClock : ℝ)=phaseOffset phase+t := by
  constructor <;> ring

theorem receiver_initial : receiver .enter 0=initialReceiver := rfl

theorem state_junctions :
    nuclearPosition .enter duration=nuclearPosition .drive 0 ∧
    nuclearPosition .drive duration=nuclearPosition .leave 0 ∧
    nuclearMomentum .enter duration=nuclearMomentum .drive 0 ∧
    nuclearMomentum .drive duration=nuclearMomentum .leave 0 ∧
    receiver .enter duration=receiver .drive 0 ∧
    receiver .drive duration=receiver .leave 0 ∧
    gammaPath .enter duration=gammaPath .drive 0 ∧
    gammaPath .drive duration=gammaPath .leave 0 ∧
    quantumPath .enter duration=quantumPath .drive 0 ∧
    quantumPath .drive duration=quantumPath .leave 0 := by
  rcases ramp_endpoints with ⟨_,b,_,_,e,_,_,_⟩
  have zero : plateauMomentum 0=initialMomentum := by funext i; simp [plateauMomentum]
  simp only [nuclearPosition,nuclearMomentum,receiver,gammaPath,electronicTime,b,e,
    ramp_position_zero,ramp_momentum_zero,progress_endpoints.1,progress_endpoints.2,zero,
    plateauReceiver,initialKinetic,quantum_finish,quantum_start,quantumInput,add_sub_cancel_right]
  trivial

theorem hamiltonian_junctions (reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) :
    jointHamiltonian .enter duration reserve r p rho resource=jointHamiltonian .drive 0 reserve r p rho resource ∧
    jointHamiltonian .drive duration reserve r p rho resource=jointHamiltonian .leave 0 reserve r p rho resource := by
  rcases ramp_endpoints with ⟨_,b,_,d,e,_,g,_⟩
  simp only [jointHamiltonian,nuclearEnergy,electronicRate,b,d,e,g,zero_mul,add_zero]
  rw [(plateau_junctions r p).1,(plateau_junctions r p).2]
  exact ⟨rfl,rfl⟩

theorem receiver_force_integral :
    receiver .leave duration-receiver .enter 0=∫ t in (0 : ℝ)..duration, -kineticRate t := by
  have regular : Continuous (fun t => -kineticRate t) := by unfold kineticRate progress progressRate; fun_prop
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => plateau_receiver_derivative t) (regular.intervalIntegrable 0 duration)
  have zero : plateauMomentum 0=initialMomentum := by funext i; simp [plateauMomentum]
  rw [integral,progress_endpoints.1,progress_endpoints.2]
  simp only [receiver,plateauReceiver,zero,initialKinetic,add_sub_cancel_right]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
