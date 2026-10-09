import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coupling
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerElectronic
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock.Pairing

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
open Force.Interface Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def jointHamiltonian (clock receiver : ℝ) (position momentum : Configuration) : ℝ :=
  Extract.Port.kinetic receiver+bodyHamiltonian clock position momentum

theorem joint_clock_velocity (clock : ℝ) :
    HasDerivAt (fun receiver => jointHamiltonian clock receiver (positionPath clock) (momentumPath clock))
      1 (onPath 1) :=
  (hasDerivAt_abs_pos (on_path_positive 1 (by norm_num))).add_const _

theorem joint_receiver_force (clock : ℝ) :
    HasDerivAt (fun coordinate => jointHamiltonian coordinate (onPath 1) (positionPath clock) (momentumPath clock))
      0 clock := (body_clock_derivative_on_path clock).const_add _

theorem joint_nuclear_force (clock : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointHamiltonian clock (onPath 1)
      (Function.update (positionPath clock) i (positionPath clock i+h)) (momentumPath clock))
      (-controlForce i) 0 :=
  (body_position_derivative clock (positionPath clock) (momentumPath clock) i).const_add _

theorem joint_nuclear_velocity (clock : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointHamiltonian clock (onPath 1) (positionPath clock)
      (Function.update (momentumPath clock) i (momentumPath clock i+h))) 0 0 :=
  (body_momentum_derivative_on_path clock i).const_add _

theorem plateau_hamilton_equations (clock : ℝ) (i : Coordinate) :
    HasDerivAt (fun t : ℝ => t) 1 clock ∧
    HasDerivAt (fun _ : ℝ => onPath 1) 0 clock ∧
    HasDerivAt (fun t => positionPath t i) 0 clock ∧
    HasDerivAt (fun t => momentumPath t i) (controlForce i) clock :=
  ⟨hasDerivAt_id clock,hasDerivAt_const clock _,position_path_derivative clock i,momentum_path_derivative clock i⟩

theorem plateau_joint_energy (clock : ℝ) :
    jointHamiltonian clock (onPath 1) (positionPath clock) (momentumPath clock)=
      baselineHamiltonian sourcePosition sourceMomentum+Extract.Port.kinetic receiverInitial := by
  rw [jointHamiltonian,body_energy_on_path,Extract.Port.kinetic,Extract.Port.kinetic,
    abs_of_pos (on_path_positive 1 (by norm_num)),abs_of_pos (lt_trans (by norm_num) receiver_initial_positive),
    on_path_exact,baselineHamiltonian,potential_at_source,nuclear_kinetic_source]
  ring

-- The source is the original M3 same-density Fock in the original symmetrized AO lift.
def referenceElectronicHamiltonian : Matrix Basis Basis ℂ :=
  Reentry.TargetFock.hamiltonian
def electronicControl : Matrix Basis Basis ℂ := -referenceElectronicHamiltonian
def electronicHamiltonian : Matrix Basis Basis ℂ := referenceElectronicHamiltonian+electronicControl

theorem electronic_hamiltonian_zero : electronicHamiltonian=0 := by
  simp [electronicHamiltonian,electronicControl]

def referenceElectronicEnergy (rho : Matrix Basis Basis ℂ) : ℝ :=
  energy referenceElectronicHamiltonian (rho-Reentry.Source.targetRealized)

theorem original_m3_fock_direction (direction : Matrix Basis Basis ℂ) (hermitian : direction.IsHermitian) :
    referenceElectronicEnergy (Reentry.Source.targetRealized+direction)=
      energy Reentry.TargetFock.fock (Reentry.TargetFock.sourceLift direction) := by
  rw [referenceElectronicEnergy,add_sub_cancel_left,referenceElectronicHamiltonian]
  exact Reentry.TargetFock.source_pairing direction hermitian

def sourceEnergyGerm (position momentum : Configuration) (rho : Matrix Basis Basis ℂ) : ℝ :=
  baselineHamiltonian position momentum+referenceElectronicEnergy rho

def controlEnergy (clock : ℝ) (position momentum : Configuration) (rho : Matrix Basis Basis ℂ) : ℝ :=
  covariantKinetic clock momentum-nuclearKinetic momentum+drivePotential position-referenceElectronicEnergy rho

def completeHamiltonian (clock receiver : ℝ) (position momentum : Configuration) (rho : Matrix Basis Basis ℂ) : ℝ :=
  Extract.Port.kinetic receiver+sourceEnergyGerm position momentum rho+controlEnergy clock position momentum rho

theorem complete_hamiltonian_exact (clock receiver : ℝ) (position momentum : Configuration) (rho : Matrix Basis Basis ℂ) :
    completeHamiltonian clock receiver position momentum rho=jointHamiltonian clock receiver position momentum := by
  unfold completeHamiltonian sourceEnergyGerm controlEnergy jointHamiltonian bodyHamiltonian baselineHamiltonian
  ring

theorem source_energy_germ_anchor :
    sourceEnergyGerm sourcePosition sourceMomentum Reentry.Source.targetRealized=
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  simp only [sourceEnergyGerm,referenceElectronicEnergy,sub_self,energy,mul_zero,Matrix.trace_zero,Complex.zero_re,
    add_zero,baselineHamiltonian,potential_at_source,nuclear_kinetic_source]

theorem quantum_energy_direction_zero (clock receiver : ℝ) (position momentum : Configuration)
    (rho direction : Matrix Basis Basis ℂ) (coordinate : ℝ) :
    HasDerivAt (fun s : ℝ => completeHamiltonian clock receiver position momentum (rho+s • direction))
      0 coordinate := by
  simp only [complete_hamiltonian_exact]
  exact hasDerivAt_const coordinate _

def electronicAction (time : ℝ) : Matrix.unitaryGroup Basis ℂ :=
  ⟨hamiltonianFlow electronicHamiltonian time,hamiltonianFlow_unitary electronicHamiltonian
    (by rw [electronic_hamiltonian_zero]; exact Matrix.isHermitian_zero) time⟩

theorem electronic_action_generated (time : ℝ) :
    (electronicAction time : Matrix Basis Basis ℂ)=hamiltonianFlow electronicHamiltonian time := rfl

theorem electronic_action_identity (time : ℝ) : electronicAction time=1 := by
  apply Subtype.ext
  change hamiltonianFlow electronicHamiltonian time=1
  simp [electronic_hamiltonian_zero,hamiltonianFlow]

def heldPath (time : ℝ) : Matrix Basis Basis ℂ :=
  conjugation (electronicAction time) Reentry.Producer.exactTarget
def realizedPath (time : ℝ) : Matrix Basis Basis ℂ :=
  conjugation (electronicAction time) Reentry.Source.targetRealized

theorem held_path_exact (time : ℝ) : heldPath time=Reentry.Producer.exactTarget := by
  simp [heldPath,electronic_action_identity,conjugation_apply]

theorem realized_path_exact (time : ℝ) : realizedPath time=Reentry.Source.targetRealized := by
  simp [realizedPath,electronic_action_identity,conjugation_apply]

theorem electronic_equation (time : ℝ) :
    HasDerivAt heldPath (-Complex.I • (electronicHamiltonian*heldPath time-heldPath time*electronicHamiltonian)) time := by
  simp only [electronic_hamiltonian_zero,zero_mul,mul_zero,sub_self,smul_zero]
  have same : heldPath=fun _ : ℝ => Reentry.Producer.exactTarget := funext held_path_exact
  rw [same]
  exact hasDerivAt_const time _

theorem realized_error_retained (time : ℝ) :
    realizedPath time=heldPath time+Reentry.Producer.inheritedResidual+Reentry.Producer.newNumericalResidual := by
  rw [realized_path_exact,held_path_exact]
  exact Reentry.Producer.total_error_reconstruction.2

theorem every_held_configuration_readout {α : Type*}
    (readout : Configuration → Matrix Basis Basis ℂ → α) (time : ℝ) :
    readout (positionPath time) (realizedPath time)=readout sourcePosition Reentry.Source.targetRealized := by
  rw [realized_path_exact]
  rfl

def targetFrame : Inertia.Interface.NuclearFrame :=
  { Reentry.Source.stepReadout.nuclear.target with
    momentum := boostedMomentum
    kinetic := boostedKinetic
    total := boostedKinetic+Reentry.Source.stepReadout.nuclear.target.potential }

theorem target_generated_by_path (i : Coordinate) :
    (targetFrame.position i.1 i.2 : ℝ)=positionPath duration i ∧
    (targetFrame.momentum i.1 i.2 : ℝ)=momentumPath duration i :=
  ⟨rfl,(momentum_endpoint i).symm⟩

theorem actual_body_change : targetFrame.momentum ≠ Reentry.Source.stepReadout.nuclear.target.momentum :=
  boosted_momentum_changed

theorem actual_positive_debit : 0 < receiverInitial-receiverTarget := by
  rw [receiver_target_debit]
  exact Rat.cast_pos.mpr boost_cost_positive_and_below_stock.1

theorem on_force_integral : onPath 1-receiverInitial=
    ∫ _x in (0 : ℝ)..1, switchForce (baselineHamiltonian sourcePosition sourceMomentum)
      (bodyHamiltonian 0 sourcePosition sourceMomentum) := switch_integral _ _ _

theorem off_force_integral : receiverTarget-onPath 1=
    ∫ _x in (0 : ℝ)..1, switchForce
      (bodyHamiltonian duration (positionPath duration) (momentumPath duration))
      (baselineHamiltonian (positionPath duration) (momentumPath duration)) := switch_integral _ _ _

theorem source_force_jet (i : Coordinate) :
    HasDerivAt (fun h => sourcePotentialGerm (Function.update sourcePosition i (sourcePosition i+h)))
      (-sourceForce i) 0 := by
  have value (h : ℝ) :
      sourcePotentialGerm (Function.update sourcePosition i (sourcePosition i+h))=sourcePotential-h*sourceForce i := by
    unfold sourcePotentialGerm
    have entry (j : Coordinate) :
        sourceForce j*(Function.update sourcePosition i (sourcePosition i+h) j-sourcePosition j)=
          if j=i then sourceForce i*h else 0 := by
      by_cases same : j=i
      · subst j; simp
      · simp [same]
    simp_rw [entry]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring
  simp_rw [value]
  simpa only [id_eq,one_mul,Pi.sub_apply,zero_sub] using!
    ((hasDerivAt_const (0 : ℝ) sourcePotential).sub ((hasDerivAt_id (0 : ℝ)).mul_const (sourceForce i)))

theorem target_mechanical_account :
    (targetFrame.total : ℝ)+Extract.Port.kinetic receiverTarget=
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential+Extract.Port.kinetic receiverInitial := by
  have account := body_receiver_energy_account
  simpa only [targetFrame,Rat.cast_add,baselineHamiltonian,positionPath,potential_at_source,
    nuclear_kinetic_source,nuclear_kinetic_target,sourcePotential] using account

theorem original_engine_account :
    (targetFrame.total : ℝ)+Extract.Port.kinetic receiverTarget-
      ((Reentry.Source.stepReadout.nuclear.current.total : ℝ)+Extract.Port.kinetic receiverInitial)=
        (Reentry.Source.engineEnergyChange : ℝ)-(Reentry.Source.engineAccountingResidual : ℝ)-
          (Reentry.Producer.targetKineticResidual : ℝ) := by
  have localAccount := original_recorded_energy_account
  have original := congrArg (fun x : ℚ => (x : ℝ)) Reentry.Producer.nuclearEngineVsPhysicalAccount
  push_cast at original
  simp only [targetFrame,Rat.cast_add]
  change (boostedKinetic : ℝ)+sourcePotential+Extract.Port.kinetic receiverTarget-
    ((Reentry.Source.stepReadout.nuclear.current.total : ℝ)+Extract.Port.kinetic receiverInitial)=_
  linarith only [localAccount,original]

def resourceBefore : Material := ControlRecovery.Runtime.readCurrent ControlRecovery.Runtime.afterSecond
def resourceAfter : Material := ⟨Live.loadNext resourceBefore.quantum,receiverTarget⟩

theorem body_resource_not_unchanged : resourceAfter.momentum ≠ resourceBefore.momentum := by
  intro same
  have debit := actual_positive_debit
  change 0 < resourceBefore.momentum-resourceAfter.momentum at debit
  rw [same,sub_self] at debit
  exact (lt_irrefl 0) debit

theorem resource_clock : resourceAfter.quantum.localClock=19*Propagation.Producer.nativeClockStep := by
  change resourceBefore.quantum.localClock+Propagation.Producer.nativeClockStep=_
  have original := ControlRecovery.Runtime.actual_clocks.2.2
  change resourceBefore.quantum.localClock=_ at original
  rw [original]
  ring

theorem resource_body_account :
    Live.freeEnergy resourceAfter.quantum+Live.entropyProduction resourceAfter.quantum+
      Extract.Port.kinetic resourceAfter.momentum+(targetFrame.total : ℝ)=
    Live.freeEnergy resourceBefore.quantum+Live.entropyProduction resourceBefore.quantum+
      Extract.Port.kinetic resourceBefore.momentum+
        (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  have hold := Live.loadNext_net_account resourceBefore.quantum
  change (Live.freeEnergy resourceAfter.quantum-Live.freeEnergy resourceBefore.quantum)+
    (Live.entropyProduction resourceAfter.quantum-Live.entropyProduction resourceBefore.quantum)=0 at hold
  have body := target_mechanical_account
  change (targetFrame.total : ℝ)+Extract.Port.kinetic resourceAfter.momentum=
    (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential+Extract.Port.kinetic resourceBefore.momentum at body
  linarith only [hold,body]

theorem full_historical_account :
    Live.freeEnergy resourceAfter.quantum+Live.entropyProduction resourceAfter.quantum+
      Extract.Port.kinetic resourceAfter.momentum+(targetFrame.total : ℝ)=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
        Extract.pulseWork Weak.execution+responseWork Replenish.origin+
          (Reentry.Source.stepReadout.nuclear.target.total : ℝ)-(Reentry.Producer.targetKineticResidual : ℝ) := by
  have previous := ControlRecovery.Runtime.complete_account ControlRecovery.Runtime.afterSecond
  change Live.freeEnergy resourceBefore.quantum+Live.entropyProduction resourceBefore.quantum+
    Extract.Port.kinetic resourceBefore.momentum=_ at previous
  have original := congrArg (fun x : ℚ => (x : ℝ)) Reentry.Producer.targetMechanicalEnergyWholeAccount
  push_cast at original
  change (Reentry.Source.stepReadout.nuclear.target.total : ℝ)=
    (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential+(Reentry.Producer.targetKineticResidual : ℝ) at original
  linarith only [resource_body_account,previous,original]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
