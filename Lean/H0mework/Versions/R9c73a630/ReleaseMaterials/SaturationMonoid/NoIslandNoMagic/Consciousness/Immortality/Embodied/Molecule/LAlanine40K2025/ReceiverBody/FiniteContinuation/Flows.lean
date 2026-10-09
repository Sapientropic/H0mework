import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Pulse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
abbrev Phase := FiniteActuation.Phase

def nuclearPosition (current : Material) : Phase → ℝ → Configuration
  | .enter => fun t => FiniteActuation.rampPosition (momentum current) (FiniteActuation.onTime t)
  | .drive => fun _ => sourcePosition
  | .leave => fun t => FiniteActuation.rampPosition (pulseMomentum current 1) (FiniteActuation.offTime t)

def nuclearMomentum (current : Material) : Phase → ℝ → Configuration
  | .enter => fun t => FiniteActuation.rampMomentum (momentum current) (FiniteActuation.onTime t)
  | .drive => fun t => pulseMomentum current (FiniteActuation.progress t)
  | .leave => fun t => FiniteActuation.rampMomentum (pulseMomentum current 1) (FiniteActuation.offTime t)

def receiver (current : Material) : Phase → ℝ → ℝ
  | .enter => fun _ => current.body.resource.momentum
  | .drive => fun t => pulseReceiver current (FiniteActuation.progress t)
  | .leave => fun _ => pulseReceiver current 1

def nuclearEnergy (current : Material) : Phase → ℝ → Configuration → Configuration → ℝ
  | .enter => fun t => FiniteActuation.rampHamiltonian (momentum current) (FiniteActuation.onTime t) (FiniteActuation.onRate t)
  | .drive => pulseHamiltonian current
  | .leave => fun t => FiniteActuation.rampHamiltonian (pulseMomentum current 1) (FiniteActuation.offTime t) (FiniteActuation.offRate t)

def quantumInput (current : Material) : Phase → Live.State
  | .enter => current.body.resource.quantum
  | .drive => Live.loadNext current.body.resource.quantum
  | .leave => Live.loadNext (Live.loadNext current.body.resource.quantum)

def quantumPath (current : Material) (phase : Phase) (t : ℝ) : PointerJoint :=
  conjugation (Pointer.loadPulse t) (quantumInput current phase).joint

def gammaPath (current : Material) (phase : Phase) (t : ℝ) : Matrix Basis Basis ℂ :=
  FiniteActuation.electronFlow current.body.realized (FiniteActuation.electronicTime phase t)

def jointHamiltonian (current : Material) (phase : Phase) (t reserve : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) : ℝ :=
  energy Pointer.baselineHamiltonian resource+Extract.Port.kinetic reserve+
    nuclearEnergy current phase t r p+FiniteActuation.electronicRate phase t*referenceElectronicEnergy rho

theorem position_at_source (current : Material) (valid : Admissible current) (i : Coordinate) :
    (current.body.frame.position i.1 i.2 : ℝ)=sourcePosition i := by
  rw [valid.position]
  exact FiniteActuation.input_position i

theorem source_realization (current : Material) (valid : Admissible current) :
    current.body.realized=current.body.held+current.body.inheritedResidual+current.body.newNumericalResidual := by
  rw [valid.realized,valid.held,valid.inheritedResidual,valid.newNumericalResidual]
  exact FiniteActuation.target_retains_residual

theorem gamma_equation (current : Material) (phase : Phase) (t : ℝ) :
    HasDerivAt (gammaPath current phase)
      (-Complex.I • (FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)*gammaPath current phase t-
        gammaPath current phase t*FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t))) t :=
  FiniteActuation.electron_equation _ _ _ _ (FiniteActuation.electronic_time_derivative phase t)

theorem gamma_centered_energy (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ) :
    referenceElectronicEnergy (gammaPath current phase t)=0 := by
  rw [gammaPath,valid.realized]
  exact FiniteActuation.electron_centered_energy _

theorem gamma_residual_retained (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ) :
    gammaPath current phase t=
      FiniteActuation.electronFlow current.body.held (FiniteActuation.electronicTime phase t)+
      FiniteActuation.electronFlow current.body.inheritedResidual (FiniteActuation.electronicTime phase t)+
      FiniteActuation.electronFlow current.body.newNumericalResidual (FiniteActuation.electronicTime phase t) := by
  rw [gammaPath,source_realization current valid]
  simp only [FiniteActuation.electronFlow,map_add]

theorem quantum_generated (current : Material) (phase : Phase) (t : ℝ) :
    quantumPath current phase t=Extract.Port.bodyFlow Pointer.baselineHamiltonian (quantumInput current phase).joint t := by
  rw [quantumPath,conjugation_apply,Pointer.loadPulse_baseline]
  rfl

theorem quantum_equation (current : Material) (phase : Phase) (t : ℝ) :
    HasDerivAt (quantumPath current phase)
      (-Complex.I • (Pointer.baselineHamiltonian*quantumPath current phase t-
        quantumPath current phase t*Pointer.baselineHamiltonian)) t := by
  change HasDerivAt (fun time => quantumPath current phase time) _ t
  simp_rw [quantum_generated]
  exact Extract.Port.body_flow_liouville _ _ Pointer.baselineHamiltonian_hermitian t

theorem quantum_start (current : Material) (phase : Phase) : quantumPath current phase 0=(quantumInput current phase).joint := by
  rw [quantum_generated]
  simp [Extract.Port.bodyFlow,hamiltonianFlow]

theorem quantum_finish (current : Material) (phase : Phase) :
    quantumPath current phase duration=(Live.loadNext (quantumInput current phase)).joint :=
  (Live.loadNext_joint (quantumInput current phase)).symm

theorem quantum_energy (current : Material) (phase : Phase) (t : ℝ) :
    energy Pointer.baselineHamiltonian (quantumPath current phase t)=Live.baselineEnergy current.body.resource.quantum := by
  rw [quantumPath,Extract.Port.Timeline.load_energy_preserved]
  change Live.baselineEnergy (quantumInput current phase)=_
  cases phase <;> simp only [quantumInput,Live.loadNext_preserves_baseline]

theorem receiver_positive (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ)
    (lo : 0 ≤ t) (hi : t ≤ duration) : 0 < receiver current phase t := by
  have half := half_pos (stock_positive current valid)
  cases phase with
  | enter => exact stock_positive current valid
  | drive => exact half.trans (pulse_stock current valid _
      (FiniteActuation.progress_range t lo hi).1 (FiniteActuation.progress_range t lo hi).2)
  | leave => exact half.trans (pulse_stock current valid 1 (by norm_num) (by norm_num))

theorem nuclear_receiver_account (current : Material) (phase : Phase) (t : ℝ) :
    receiver current phase t+nuclearEnergy current phase t (nuclearPosition current phase t) (nuclearMomentum current phase t)=
      current.body.resource.momentum+nuclearKinetic (momentum current)+sourcePotential := by
  cases phase with
  | enter =>
      dsimp only [receiver,nuclearEnergy,nuclearPosition,nuclearMomentum]
      rw [FiniteActuation.ramp_energy]
      ring
  | drive => exact pulse_energy_account current t
  | leave =>
      dsimp only [receiver,nuclearEnergy,nuclearPosition,nuclearMomentum]
      rw [FiniteActuation.ramp_energy,pulseReceiver]
      ring

theorem phase_energy_account (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ)
    (lo : 0 ≤ t) (hi : t ≤ duration) :
    jointHamiltonian current phase t (receiver current phase t) (nuclearPosition current phase t)
      (nuclearMomentum current phase t) (gammaPath current phase t) (quantumPath current phase t)=
    Live.baselineEnergy current.body.resource.quantum+current.body.resource.momentum+
      nuclearKinetic (momentum current)+sourcePotential := by
  rw [jointHamiltonian,quantum_energy,Extract.Port.kinetic,abs_of_pos (receiver_positive current valid phase t lo hi),
    gamma_centered_energy current valid,mul_zero,add_zero]
  have nuclear := nuclear_receiver_account current phase t
  linarith only [nuclear]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
