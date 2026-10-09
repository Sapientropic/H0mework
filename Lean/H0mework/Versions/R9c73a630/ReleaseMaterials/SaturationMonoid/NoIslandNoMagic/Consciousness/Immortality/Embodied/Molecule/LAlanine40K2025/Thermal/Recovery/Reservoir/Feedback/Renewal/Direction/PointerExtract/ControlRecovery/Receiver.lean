import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Gain
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Receiver
open Collision Quantum Resource Propagation.Producer Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def controlHamiltonian : PointerJoint :=
  Charging.Pulse.pulseHamiltonian recoveredPointerControl (nativeClockStep : ℝ)

theorem control_hermitian : controlHamiltonian.IsHermitian :=
  Charging.Pulse.pulseHamiltonian_hermitian _ _

private def generatedPulse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (time : ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨hamiltonianFlow H time,hamiltonianFlow_unitary H hH time⟩

def pulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ := generatedPulse controlHamiltonian control_hermitian time

theorem pulse_clock : pulse (nativeClockStep : ℝ)=recoveredPointerControl := by
  apply Subtype.ext
  exact Charging.Pulse.pulseHamiltonian_generates _ _
    (by exact_mod_cast nativeClockStep_positive.ne')

private theorem generated_conserves {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (time : ℝ) :
    energy H (conjugation (generatedPulse H hH time) rho)=energy H rho := by
  simpa only [conjugation_apply] using
    PreparationEnergy.commuting_energy H rho (generatedPulse H hH time) (matrix_generator_commutes H time)

theorem pulse_conserves (time : ℝ) (rho : PointerJoint) :
    energy controlHamiltonian (conjugation (pulse time) rho)=energy controlHamiltonian rho :=
  generated_conserves _ _ _ _

def offset : ℝ := ‖Pointer.baselineHamiltonian‖+‖controlHamiltonian‖+1
def coupledHamiltonian : PointerJoint := controlHamiltonian-offset • (1 : PointerJoint)

theorem coupled_hermitian : coupledHamiltonian.IsHermitian :=
  control_hermitian.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint offset from rfl))

theorem coupled_conserved (time : ℝ) (rho : PointerJoint) (trace : rho.trace=1) :
    energy coupledHamiltonian (conjugation (pulse time) rho)=energy coupledHamiltonian rho := by
  rw [coupledHamiltonian,Extract.Port.Launch.scalar_shift_energy _ _ _ ((conjugation_trace _ _).trans trace),
    Extract.Port.Launch.scalar_shift_energy _ _ _ trace,pulse_conserves]

private theorem shifted_generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (c time : ℝ) :
    time • (-Complex.I • (H-c • (1 : Matrix ι ι ℂ)))=
      time • (-Complex.I • H)+(Complex.I*(c : ℂ)*(time : ℂ)) • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul,Complex.real_smul]
  ring

def phase (time : ℝ) : unitary ℂ :=
  ⟨NormedSpace.exp (Complex.I*(offset : ℂ)*(time : ℂ)),by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp only [star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring⟩

def coupledPulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ := phase time • pulse time

theorem pulse_is_coupled_flow (time : ℝ) :
    (coupledPulse time : PointerJoint)=hamiltonianFlow coupledHamiltonian time := by
  rw [hamiltonianFlow,coupledHamiltonian,shifted_generator,Pointer.exp_scalar_shift]
  rfl

theorem coupled_pulse_density (time : ℝ) (rho : PointerJoint) :
    conjugation (coupledPulse time) rho=conjugation (pulse time) rho := unitPhase_conjugation _ _ _

def quantumNext (current : Live.State) : Live.State :=
  ⟨current.localClock+nativeClockStep,coupledPulse (nativeClockStep : ℝ)*current.action⟩

theorem next_joint (current : Live.State) :
    (quantumNext current).joint=conjugation (coupledPulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

theorem next_projection (current : Live.State) :
    (quantumNext current).joint=(recoveredNext current).joint := by
  rw [next_joint,coupled_pulse_density,pulse_clock,recovered_next_joint]

theorem next_coupled_conserved (current : Live.State) :
    energy coupledHamiltonian (quantumNext current).joint=energy coupledHamiltonian current.joint := by
  rw [next_joint,coupled_pulse_density]
  exact coupled_conserved _ _ current.normalized

def onMomentum (input : Material) : ℝ :=
  Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian input.quantum.joint input.momentum 1

def advance (input : Material) : Material :=
  let target := quantumNext input.quantum
  ⟨target,Extract.Port.momentumPath coupledHamiltonian Pointer.baselineHamiltonian target.joint (onMomentum input) 1⟩

def output : Material := advance material

theorem source_zero : material.momentum=0 := by
  rw [source_exact]
  exact Replenish.Account.receiver_empty

theorem output_clock : output.quantum.localClock=17*nativeClockStep := recovered_clock

theorem output_projection : output.quantum.joint=(recoveredNext origin).joint := next_projection origin

theorem output_gain : (2/25 : ℝ) < Live.baselineEnergy material.quantum-Live.baselineEnergy output.quantum := by
  change (2/25 : ℝ) < energy Pointer.baselineHamiltonian origin.joint-energy Pointer.baselineHamiltonian output.quantum.joint
  rw [output_projection]
  exact recovered_actual_total_gain

theorem on_balance (input : Material) :
    energy coupledHamiltonian input.quantum.joint+onMomentum input=
      energy Pointer.baselineHamiltonian input.quantum.joint+input.momentum := by
  simpa only [(Extract.Port.switch_path_endpoints Pointer.baselineHamiltonian coupledHamiltonian).2,onMomentum] using
    Extract.Port.switch_path_conserved Pointer.baselineHamiltonian coupledHamiltonian input.quantum.joint input.momentum 1

theorem off_balance (input : Material) :
    energy Pointer.baselineHamiltonian (advance input).quantum.joint+(advance input).momentum=
      energy coupledHamiltonian (advance input).quantum.joint+onMomentum input := by
  simpa only [(Extract.Port.switch_path_endpoints coupledHamiltonian Pointer.baselineHamiltonian).2,advance] using
    Extract.Port.switch_path_conserved coupledHamiltonian Pointer.baselineHamiltonian
      (quantumNext input.quantum).joint (onMomentum input) 1

theorem momentum_gain (input : Material) :
    (advance input).momentum-input.momentum=
      Live.baselineEnergy input.quantum-Live.baselineEnergy (advance input).quantum := by
  have first := on_balance input
  have last := off_balance input
  have hold := next_coupled_conserved input.quantum
  change energy coupledHamiltonian (advance input).quantum.joint=energy coupledHamiltonian input.quantum.joint at hold
  change _=energy Pointer.baselineHamiltonian input.quantum.joint-
    energy Pointer.baselineHamiltonian (advance input).quantum.joint
  linarith only [first,last,hold]

theorem output_momentum : (2/25 : ℝ) < output.momentum := by
  have balance := momentum_gain material
  rw [source_zero,sub_zero] at balance
  change output.momentum=Live.baselineEnergy material.quantum-Live.baselineEnergy output.quantum at balance
  rw [balance]
  exact output_gain

theorem output_kinetic :
    (2/25 : ℝ) < Extract.Port.kinetic output.momentum-Extract.Port.kinetic material.momentum := by
  have positive : 0 < output.momentum := lt_trans (by norm_num) output_momentum
  simpa only [Extract.Port.kinetic,source_zero,abs_zero,sub_zero,abs_of_pos positive] using output_momentum

theorem source_energy_conserved :
    Live.baselineEnergy output.quantum+Extract.Port.kinetic output.momentum=
      Live.baselineEnergy material.quantum+Extract.Port.kinetic material.momentum := by
  have balance := momentum_gain material
  have positive : 0 < output.momentum := lt_trans (by norm_num) output_momentum
  change output.momentum-material.momentum=Live.baselineEnergy material.quantum-Live.baselineEnergy output.quantum at balance
  rw [source_zero,sub_zero] at balance
  rw [Extract.Port.kinetic,Extract.Port.kinetic,source_zero,abs_zero,add_zero,abs_of_pos positive,balance]
  ring

private theorem zero_launch_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H0 Hc rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (trace : rho.trace=1) :
    1 ≤ Extract.Port.momentumPath H0 (Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix ι ι ℂ)) rho 0 1 := by
  let shifted := Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix ι ι ℂ)
  have balance : energy shifted rho+Extract.Port.momentumPath H0 shifted rho 0 1=energy H0 rho+0 := by
    simpa only [(Extract.Port.switch_path_endpoints H0 shifted).2] using Extract.Port.switch_path_conserved H0 shifted rho 0 1
  dsimp only [shifted] at balance
  rw [Extract.Port.Launch.scalar_shift_energy _ _ _ trace] at balance
  have bound := Extract.Port.force_bound H0 Hc rho positive trace
  have force : Extract.Port.force H0 Hc rho=energy H0 rho-energy Hc rho := by
    simp only [Extract.Port.force,energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
    ring
  rw [force] at bound
  linarith only [balance,(abs_le.mp bound).1]

theorem on_source_lower : 1 ≤ onMomentum material := by
  rw [onMomentum,source_zero,coupledHamiltonian,offset]
  exact zero_launch_lower _ _ _ material.quantum.positive material.quantum.normalized

theorem on_force_integral (input : Material) : onMomentum input-input.momentum=
    ∫ _x in (0 : ℝ)..1, Extract.Port.force Pointer.baselineHamiltonian coupledHamiltonian input.quantum.joint :=
  Extract.Port.momentum_path_integral _ _ _ _

theorem off_force_integral (input : Material) : (advance input).momentum-onMomentum input=
    ∫ _x in (0 : ℝ)..1, Extract.Port.force coupledHamiltonian Pointer.baselineHamiltonian (advance input).quantum.joint :=
  Extract.Port.momentum_path_integral _ _ _ _

def onPath (s : ℝ) : ℝ :=
  Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian origin.joint 0 s
def offPath (s : ℝ) : ℝ :=
  Extract.Port.momentumPath coupledHamiltonian Pointer.baselineHamiltonian output.quantum.joint (onMomentum material) s

theorem on_path_nonnegative (s : ℝ) (lo : 0 ≤ s) : 0 ≤ onPath s := by
  have linear : onPath s=s*onMomentum material := by
    simp only [onPath,onMomentum,origin,Extract.Port.momentumPath,source_zero,zero_add,one_mul]
  rw [linear]
  exact mul_nonneg lo (le_trans (by norm_num) on_source_lower)

theorem off_path_positive (s : ℝ) (lo : 0 ≤ s) (hi : s ≤ 1) : 0 < offPath s := by
  have linear : offPath s=(1-s)*onMomentum material+s*output.momentum := by
    change onMomentum material+s*Extract.Port.force coupledHamiltonian Pointer.baselineHamiltonian output.quantum.joint=
      (1-s)*onMomentum material+s*(onMomentum material+1*Extract.Port.force coupledHamiltonian Pointer.baselineHamiltonian output.quantum.joint)
    ring
  have start : 0 < onMomentum material := lt_of_lt_of_le (by norm_num) on_source_lower
  have finish : 0 < output.momentum := lt_trans (by norm_num) output_momentum
  rw [linear]
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) start.le,mul_nonneg lo finish.le]

def plateau (time : ℝ) : PointerJoint := conjugation (coupledPulse time) origin.joint

theorem plateau_flow (time : ℝ) : plateau time=Extract.Port.bodyFlow coupledHamiltonian origin.joint time := by
  rw [plateau,conjugation_apply,pulse_is_coupled_flow]
  rfl

theorem plateau_equation (time : ℝ) :
    HasDerivAt plateau (-Complex.I • (coupledHamiltonian*plateau time-plateau time*coupledHamiltonian)) time := by
  change HasDerivAt (fun t => plateau t) _ time
  simp only [plateau_flow]
  exact Extract.Port.body_flow_liouville coupledHamiltonian origin.joint coupled_hermitian time

private theorem generated_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) : conjugation (generatedPulse H hH 0) rho=rho := by
  simp [generatedPulse,hamiltonianFlow,conjugation_apply]

theorem plateau_initial : plateau 0=origin.joint := by
  rw [plateau,coupled_pulse_density]
  exact generated_zero controlHamiltonian origin.joint control_hermitian

theorem plateau_target : plateau (nativeClockStep : ℝ)=output.quantum.joint := by
  exact (next_joint origin).symm

theorem plateau_energy (time : ℝ) :
    energy coupledHamiltonian (plateau time)+Extract.Port.kinetic (onMomentum material)=
      Live.baselineEnergy origin+Extract.Port.kinetic material.momentum := by
  have positive : 0 < onMomentum material := lt_of_lt_of_le (by norm_num) on_source_lower
  rw [plateau,coupled_pulse_density,coupled_conserved _ _ origin.normalized,Extract.Port.kinetic,Extract.Port.kinetic,
    source_zero,abs_zero,add_zero,abs_of_pos positive]
  simpa only [origin,Live.baselineEnergy,source_zero,add_zero] using on_balance material

theorem output_memory : oneRead output.quantum.joint=oneRead origin.joint := by
  rw [output_projection,recovered_next_joint]
  exact blockUnitary_preserves_oneRead _ _ _

theorem output_donor : donorMatrixOf (bodyRead output.quantum.joint)=donorMatrixOf (bodyRead origin.joint) := by
  rw [output_projection,recovered_next_joint]
  exact recovered_donor _

theorem output_environment : Powered.Dynamics.controllerReduce (bodyRead output.quantum.joint)=
    Powered.Dynamics.controllerReduce (bodyRead origin.joint) := by
  rw [output_projection,recovered_next_joint]
  exact recovered_environment _

theorem output_remaining : donorRemainingOf (suppliedBlock output.quantum)=donorRemainingOf (suppliedBlock origin) := by
  have block : suppliedBlock output.quantum=conjugation recoveredBodyControl (suppliedBlock origin) := by
    change output.quantum.joint.toBlocks₂₂=_
    rw [output_projection,recovered_next_joint]
    exact controlled_block_right _ _ _
  rw [block]
  unfold donorRemainingOf donorEnergyOf
  rw [recovered_body_donor,conjugation_trace]

theorem source_net_account :
    Live.freeEnergy output.quantum+Live.entropyProduction output.quantum+Extract.Port.kinetic output.momentum=
      Live.freeEnergy material.quantum+Live.entropyProduction material.quantum := by
  have first := Live.complete_account material.quantum
  have last := Live.complete_account output.quantum
  have paid := source_energy_conserved
  rw [source_zero,show Extract.Port.kinetic 0=0 by simp [Extract.Port.kinetic],add_zero] at paid
  linarith only [first,last,paid]

theorem original_input : origin=Replenish.Registered.execution := by
  have h := congrArg (fun input : Material => input.quantum) source_exact
  exact h.trans Replenish.Account.output_quantum

theorem full_historical_account :
    Live.freeEnergy output.quantum+Live.entropyProduction output.quantum+Extract.Port.kinetic output.momentum=
      Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
        responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
          Extract.pulseWork Weak.execution+responseWork Replenish.origin := by
  rw [source_net_account]
  change Live.freeEnergy origin+Live.entropyProduction origin=_
  rw [original_input]
  exact Replenish.Account.full_historical_account

theorem full_historical_debit :
    donorRemainingOf (suppliedBlock output.quantum)+Replenish.Registered.transfer+Weak.transfer+
      supplyTransfer received+supplyTransfer receivedState=donorRemainingOf (suppliedBlock receivedState) := by
  rw [output_remaining,original_input]
  exact Replenish.Account.full_historical_debit

theorem output_changed : output.quantum.joint ≠ origin.joint := by
  intro same
  have gain := output_gain
  change (2/25 : ℝ) < energy Pointer.baselineHamiltonian origin.joint-
    energy Pointer.baselineHamiltonian output.quantum.joint at gain
  rw [same,sub_self] at gain
  norm_num at gain

theorem output_not_load : output.quantum ≠ Live.loadNext origin := by
  intro same
  have gain := output_gain
  change (2/25 : ℝ) < Live.baselineEnergy origin-Live.baselineEnergy output.quantum at gain
  rw [same,Live.loadNext_preserves_baseline,sub_self] at gain
  norm_num at gain

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Receiver
