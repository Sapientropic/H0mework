import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Runtime.Consumers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! A source-fixed impulsive port model with separately prepared initial stock.
The switch coordinate parameterizes a zero-duration quench, not a finite-time
Schrödinger trajectory. Only the plateau advances the original quantum clock. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port
open Collision Quantum Load.Producer.StrictThermal Load.Producer.HeatProbability
open Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def switchHamiltonian (old new : Matrix ι ι ℂ) (coordinate : ℝ) : Matrix ι ι ℂ :=
  old + coordinate • (new-old)

def force (old new rho : Matrix ι ι ℂ) : ℝ := -energy (new-old) rho

def momentumPath (old new rho : Matrix ι ι ℂ) (initial : ℝ) (coordinate : ℝ) : ℝ :=
  initial + coordinate*force old new rho

def kinetic (momentum : ℝ) : ℝ := |momentum|

def portHamiltonian (old new rho : Matrix ι ι ℂ) (coordinate momentum : ℝ) : ℝ :=
  kinetic momentum+energy (switchHamiltonian old new coordinate) rho

theorem switch_hamiltonian_derivative (old new : Matrix ι ι ℂ) (coordinate : ℝ) :
    HasDerivAt (switchHamiltonian old new) (new-old) coordinate := by
  simpa only [switchHamiltonian,one_smul,id_eq] using!
    (((hasDerivAt_id coordinate).smul_const (new-old)).const_add old)

theorem switch_potential_force (old new rho : Matrix ι ι ℂ) (coordinate : ℝ) :
    HasDerivAt (fun x => energy (switchHamiltonian old new x) rho) (-force old new rho) coordinate := by
  have curve (x : ℝ) : energy (switchHamiltonian old new x) rho =
      energy old rho+x*energy (new-old) rho := by
    simp [switchHamiltonian,energy,Matrix.add_mul,Matrix.trace_add,Matrix.trace_smul]
  simp_rw [curve]
  simpa only [force,neg_neg,one_mul,id_eq] using!
    (((hasDerivAt_id coordinate).mul_const (energy (new-old) rho)).const_add (energy old rho))

omit [DecidableEq ι] in
theorem momentum_path_derivative (old new rho : Matrix ι ι ℂ) (initial coordinate : ℝ) :
    HasDerivAt (momentumPath old new rho initial) (force old new rho) coordinate := by
  simpa only [momentumPath,one_mul,id_eq] using!
    (((hasDerivAt_id coordinate).mul_const (force old new rho)).const_add initial)

omit [DecidableEq ι] in
theorem canonical_velocity (old new rho : Matrix ι ι ℂ) (coordinate momentum : ℝ)
    (positive : 0 < momentum) :
    HasDerivAt (portHamiltonian old new rho coordinate) 1 momentum := by
  exact (hasDerivAt_abs_pos positive).add_const _

theorem canonical_force (old new rho : Matrix ι ι ℂ) (coordinate momentum : ℝ) :
    HasDerivAt (fun x => portHamiltonian old new rho x momentum) (-force old new rho) coordinate :=
  (switch_potential_force old new rho coordinate).const_add (kinetic momentum)

theorem switch_path_conserved (old new rho : Matrix ι ι ℂ) (initial coordinate : ℝ) :
    energy (switchHamiltonian old new coordinate) rho+momentumPath old new rho initial coordinate =
      energy old rho+initial := by
  simp [switchHamiltonian,momentumPath,force,energy,Matrix.add_mul,
    Matrix.trace_add,Matrix.trace_smul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem switch_path_endpoints (old new : Matrix ι ι ℂ) :
    switchHamiltonian old new 0=old ∧ switchHamiltonian old new 1=new := by
  simp [switchHamiltonian]

omit [DecidableEq ι] in
theorem momentum_path_integral (old new rho : Matrix ι ι ℂ) (initial : ℝ) :
    momentumPath old new rho initial 1-initial = ∫ _x in (0 : ℝ)..1, force old new rho := by
  simp [momentumPath]

theorem force_bound (old new rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace=1) :
    |force old new rho| ≤ ‖old‖+‖new‖ := by
  rw [force,abs_neg]
  exact (energy_abs_le_norm _ _ positive normalized).trans
    ((norm_sub_le new old).trans_eq (add_comm _ _))

theorem finite_momentum_path (old new rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace=1) (initial coordinate : ℝ) (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) :
    |momentumPath old new rho initial coordinate-initial| ≤ ‖old‖+‖new‖ := by
  have h := force_bound old new rho positive normalized
  rw [momentumPath,add_sub_cancel_left,abs_mul,abs_of_nonneg lo]
  exact (mul_le_mul_of_nonneg_right hi (abs_nonneg _)).trans (by simpa only [one_mul] using h)

theorem unchanged_switch_momentum (H rho : Matrix ι ι ℂ) (initial : ℝ) :
    momentumPath H H rho initial 1=initial := by
  simp [momentumPath,force,energy]

attribute [local irreducible] Weak.execution pointerControlHamiltonian Pointer.baselineHamiltonian

def initialJoint : PointerJoint := (Runtime.readCurrent Runtime.seed).joint

def controlledJoint : PointerJoint := conjugation (pointerPulse (Propagation.Producer.nativeClockStep : ℝ)) initialJoint

def sourceOn (initial : ℝ) : ℝ :=
  momentumPath Pointer.baselineHamiltonian pointerControlHamiltonian initialJoint initial 1

def sourceOff (initial : ℝ) : ℝ :=
  momentumPath pointerControlHamiltonian Pointer.baselineHamiltonian controlledJoint (sourceOn initial) 1

attribute [local irreducible] initialJoint controlledJoint

theorem controlled_joint_exact :
    controlledJoint=(Runtime.readCurrent Runtime.afterFirst).joint := by
  rw [controlledJoint,initialJoint]
  exact (Extract.next_joint Weak.execution).symm

theorem source_on_balance (initial : ℝ) :
    energy pointerControlHamiltonian initialJoint+sourceOn initial =
      energy Pointer.baselineHamiltonian initialJoint+initial := by
  simpa only [(switch_path_endpoints Pointer.baselineHamiltonian pointerControlHamiltonian).2,sourceOn] using
    switch_path_conserved Pointer.baselineHamiltonian pointerControlHamiltonian initialJoint initial 1

theorem source_pulse_balance (initial : ℝ) :
    energy pointerControlHamiltonian controlledJoint+sourceOn initial =
      energy pointerControlHamiltonian initialJoint+sourceOn initial := by
  rw [controlledJoint,pointer_control_conserved]

theorem source_off_balance (initial : ℝ) :
    energy Pointer.baselineHamiltonian controlledJoint+sourceOff initial =
      energy pointerControlHamiltonian controlledJoint+sourceOn initial := by
  simpa only [(switch_path_endpoints pointerControlHamiltonian Pointer.baselineHamiltonian).2,sourceOff] using
    switch_path_conserved pointerControlHamiltonian Pointer.baselineHamiltonian controlledJoint (sourceOn initial) 1

private theorem baseline_state_read (current : Live.State) :
    Live.baselineEnergy current=energy Pointer.baselineHamiltonian current.joint := rfl

theorem source_momentum_gain (initial : ℝ) :
    sourceOff initial-initial= -pulseWork (Runtime.readCurrent Runtime.seed) := by
  have on := source_on_balance initial
  have hold := source_pulse_balance initial
  have off := source_off_balance initial
  have work := pulse_work_actual Weak.execution
  have origin : Weak.execution.joint=initialJoint := by rw [initialJoint]; rfl
  have target : (Extract.next Weak.execution).joint=controlledJoint := controlled_joint_exact.symm
  rw [baseline_state_read,baseline_state_read,target,origin] at work
  rw [Runtime.actual_sequence.1]
  linarith only [on,hold,off,work]

theorem source_momentum_gain_positive (initial : ℝ) :
    (7/5 : ℝ) < sourceOff initial-initial := by
  rw [source_momentum_gain]
  exact Runtime.actual_net_output

theorem pulse_alone_has_no_momentum_gain (initial : ℝ) :
    momentumPath pointerControlHamiltonian pointerControlHamiltonian initialJoint initial 1=initial := by
  exact unchanged_switch_momentum _ _ _

def switchingSize : ℝ := ‖Pointer.baselineHamiltonian‖+‖pointerControlHamiltonian‖

def preparationBudget : ℝ := 2*switchingSize

def sourceOffPath (initial coordinate : ℝ) : ℝ :=
  momentumPath pointerControlHamiltonian Pointer.baselineHamiltonian controlledJoint (sourceOn initial) coordinate

theorem initial_joint_positive : initialJoint.PosSemidef := by
  rw [initialJoint]
  exact Weak.execution.positive

theorem initial_joint_trace : initialJoint.trace=1 := by
  rw [initialJoint]
  exact Weak.execution.normalized

theorem controlled_joint_positive : controlledJoint.PosSemidef := by
  rw [controlledJoint]
  exact conjugation_posSemidef _ _ initial_joint_positive

theorem controlled_joint_trace : controlledJoint.trace=1 := by
  rw [controlledJoint,conjugation_trace,initial_joint_trace]

theorem switching_size_nonnegative : 0 ≤ switchingSize := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem source_on_path_bound (initial coordinate : ℝ) (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) :
    |momentumPath Pointer.baselineHamiltonian pointerControlHamiltonian initialJoint initial coordinate-initial| ≤ switchingSize :=
  finite_momentum_path _ _ _ initial_joint_positive initial_joint_trace _ _ lo hi

theorem source_off_path_bound (initial coordinate : ℝ) (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) :
    |sourceOffPath initial coordinate-initial| ≤ preparationBudget := by
  have first := source_on_path_bound initial 1 (by norm_num) (by norm_num)
  have second := finite_momentum_path pointerControlHamiltonian Pointer.baselineHamiltonian controlledJoint
    controlled_joint_positive controlled_joint_trace (sourceOn initial) coordinate lo hi
  change |sourceOn initial-initial| ≤ switchingSize at first
  change |sourceOffPath initial coordinate-sourceOn initial| ≤ _ at second
  have same : ‖pointerControlHamiltonian‖+‖Pointer.baselineHamiltonian‖=switchingSize := add_comm _ _
  rw [same] at second
  have triangle := abs_sub_le (sourceOffPath initial coordinate) (sourceOn initial) initial
  dsimp only [preparationBudget]
  linarith only [triangle,first,second]

theorem prepared_on_positive (initial coordinate : ℝ) (paid : preparationBudget < initial)
    (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) :
    0 < momentumPath Pointer.baselineHamiltonian pointerControlHamiltonian initialJoint initial coordinate := by
  have bound := (abs_le.mp (source_on_path_bound initial coordinate lo hi)).1
  dsimp only [preparationBudget] at paid
  linarith only [paid,bound,switching_size_nonnegative]

theorem prepared_off_positive (initial coordinate : ℝ) (paid : preparationBudget < initial)
    (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) : 0 < sourceOffPath initial coordinate := by
  have bound := (abs_le.mp (source_off_path_bound initial coordinate lo hi)).1
  linarith only [paid,bound]

structure ClockBody where
  body : PointerJoint
  position : ℝ
  momentum : ℝ

def prepared (initial : ℝ) : ClockBody := ⟨initialJoint,0,initial⟩

def pulsePath (initial time : ℝ) : ClockBody :=
  ⟨conjugation (pointerPulse time) initialJoint,time,sourceOn initial⟩

def completed (initial : ℝ) : ClockBody :=
  ⟨controlledJoint,(Propagation.Producer.nativeClockStep : ℝ),sourceOff initial⟩

theorem completed_source_projection (initial : ℝ) :
    (completed initial).body=(Runtime.readCurrent Runtime.afterFirst).joint ∧
      (completed initial).position=(Propagation.Producer.nativeClockStep : ℝ) :=
  ⟨controlled_joint_exact,rfl⟩

theorem receiver_energy_gain (initial : ℝ) (paid : preparationBudget < initial) :
    kinetic (completed initial).momentum-kinetic (prepared initial).momentum =
      -pulseWork (Runtime.readCurrent Runtime.seed) := by
  have origin : 0 < initial := lt_of_le_of_lt (mul_nonneg (by norm_num) switching_size_nonnegative) paid
  have target : 0 < sourceOff initial := prepared_off_positive initial 1 paid (by norm_num) (by norm_num)
  change |sourceOff initial|-|initial|=_
  rw [abs_of_pos target,abs_of_pos origin,source_momentum_gain]

theorem receiver_energy_gain_positive (initial : ℝ) (paid : preparationBudget < initial) :
    (7/5 : ℝ) < kinetic (completed initial).momentum-kinetic (prepared initial).momentum := by
  rw [receiver_energy_gain initial paid]
  exact Runtime.actual_net_output

theorem finite_receiver_energy (initial : ℝ) (paid : preparationBudget < initial) :
    0 < kinetic (completed initial).momentum ∧
      kinetic (completed initial).momentum ≤ initial+preparationBudget := by
  have target : 0 < sourceOff initial := prepared_off_positive initial 1 paid (by norm_num) (by norm_num)
  change 0 < |sourceOff initial| ∧ |sourceOff initial| ≤ _
  rw [abs_of_pos target]
  have bound : |sourceOff initial-initial| ≤ preparationBudget :=
    source_off_path_bound initial 1 (by norm_num) (by norm_num)
  exact ⟨target,by linarith only [(abs_le.mp bound).2]⟩

def bodyFlow (H rho : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ :=
  hamiltonianFlow H time*rho*star (hamiltonianFlow H time)

theorem body_flow_derivative (H rho : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    HasDerivAt (bodyFlow H rho)
      (hamiltonianFlow H time*(-Complex.I • (H*rho-rho*H))*star (hamiltonianFlow H time)) time := by
  have derivative := ((hamiltonianFlow_derivative H time).mul_const rho).mul
    (hamiltonianFlow_derivative H time).star
  apply derivative.congr_deriv
  simp only [star_mul,star_smul,star_neg,Complex.star_def,Complex.conj_I,neg_neg,
    hermitian.isSelfAdjoint.star_eq,smul_mul_assoc,mul_smul_comm,smul_sub,sub_mul,mul_sub,mul_assoc]
  module

theorem body_flow_liouville (H rho : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    HasDerivAt (bodyFlow H rho) (-Complex.I • (H*bodyFlow H rho time-bodyFlow H rho time*H)) time := by
  apply (body_flow_derivative H rho hermitian time).congr_deriv
  have forward : Commute H (hamiltonianFlow H time) := matrix_generator_commutes H time
  have backward : Commute H (star (hamiltonianFlow H time)) := by
    have h := forward.star_star
    simpa only [hermitian.isSelfAdjoint.star_eq] using h
  unfold bodyFlow
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub,mul_sub,sub_mul,mul_assoc]
  rw [← mul_assoc (hamiltonianFlow H time) H,← forward.eq,mul_assoc H,backward.eq]

theorem pulse_matrix_flow (time : ℝ) :
    (pointerPulse time : PointerJoint)=hamiltonianFlow pointerControlHamiltonian time := by
  rw [pointer_pulse_exp,hamiltonianFlow]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  ring

theorem pulse_body_flow (initial time : ℝ) :
    (pulsePath initial time).body=bodyFlow pointerControlHamiltonian initialJoint time := by
  rw [pulsePath,conjugation_apply,pulse_matrix_flow]
  rfl

theorem source_quantum_equation (initial time : ℝ) :
    HasDerivAt (fun t => (pulsePath initial t).body)
      (-Complex.I • (pointerControlHamiltonian*(pulsePath initial time).body-
        (pulsePath initial time).body*pointerControlHamiltonian)) time := by
  simp only [pulse_body_flow]
  exact body_flow_liouville _ _ pointer_control_hermitian time

theorem source_clock_equation (initial time : ℝ) :
    HasDerivAt (fun t => (pulsePath initial t).position) 1 time := hasDerivAt_id time

theorem source_momentum_equation (initial time : ℝ) :
    HasDerivAt (fun t => (pulsePath initial t).momentum) 0 time := hasDerivAt_const time (sourceOn initial)

theorem complete_port_energy (initial : ℝ) (paid : preparationBudget < initial) :
    energy Pointer.baselineHamiltonian (completed initial).body+kinetic (completed initial).momentum =
      energy Pointer.baselineHamiltonian (prepared initial).body+kinetic (prepared initial).momentum := by
  have receiver := receiver_energy_gain initial paid
  have actual := pulse_work_actual Weak.execution
  rw [baseline_state_read,baseline_state_read] at actual
  have origin : Weak.execution.joint=(prepared initial).body := by rw [prepared,initialJoint]; rfl
  have target : (Extract.next Weak.execution).joint=(completed initial).body := controlled_joint_exact.symm
  rw [origin,target] at actual
  rw [Runtime.actual_sequence.1] at receiver
  linarith only [receiver,actual]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
