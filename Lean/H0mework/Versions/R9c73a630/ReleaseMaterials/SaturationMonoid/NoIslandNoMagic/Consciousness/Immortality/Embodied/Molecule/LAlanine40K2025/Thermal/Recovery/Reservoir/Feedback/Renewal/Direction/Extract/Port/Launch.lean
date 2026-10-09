import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Port.Timeline
/-! A new source-fixed impulsive receiver coupling, initialized with zero kinetic energy.
The scalar plateau potential participates in both switch forces and the complete energy bill.
The quantum-density projections agree with the original extraction/load occurrences;
this module does not install the additional receiver into their runtime. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.Launch
open Collision Quantum Load.Producer.StrictThermal Load.Producer.HeatProbability
open Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_shift_energy (H rho : Matrix ι ι ℂ) (c : ℝ) (trace : rho.trace=1) :
    energy (H-c • (1 : Matrix ι ι ℂ)) rho=energy H rho-c := by
  simp [energy,Matrix.sub_mul,Matrix.trace_sub,Matrix.trace_smul,trace]

theorem scalar_shift_commutator (H rho : Matrix ι ι ℂ) (c : ℝ) :
    (H-c • (1 : Matrix ι ι ℂ))*rho-rho*(H-c • (1 : Matrix ι ι ℂ))=H*rho-rho*H := by
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one]
  abel

attribute [local irreducible] Weak.execution pointerControlHamiltonian Pointer.baselineHamiltonian initialJoint controlledJoint

/-- A new scalar interaction in the plateau; its switching work is included below. -/
def offset : ℝ := switchingSize+1

def coupledControl : PointerJoint := pointerControlHamiltonian-offset • (1 : PointerJoint)

def launchPath (s : ℝ) : ℝ := momentumPath Pointer.baselineHamiltonian coupledControl initialJoint 0 s

def launched : ℝ := launchPath 1

def releasePath (s : ℝ) : ℝ := momentumPath coupledControl Pointer.baselineHamiltonian controlledJoint launched s

def released : ℝ := releasePath 1

attribute [local irreducible] coupledControl

theorem launch_balance : energy coupledControl initialJoint+launched=energy Pointer.baselineHamiltonian initialJoint := by
  simpa only [(switch_path_endpoints Pointer.baselineHamiltonian coupledControl).2,launched,launchPath,add_zero] using
    switch_path_conserved Pointer.baselineHamiltonian coupledControl initialJoint 0 1

theorem launch_from_original_force : launched=sourceOn 0+offset := by
  have original := source_on_balance 0
  have actual := launch_balance
  rw [coupledControl,scalar_shift_energy _ _ _ initial_joint_trace] at actual
  linarith only [original,actual]

theorem launch_positive : 1 ≤ launched := by
  have bound := (abs_le.mp (source_on_path_bound 0 1 (by norm_num) (by norm_num))).1
  change -switchingSize ≤ sourceOn 0-0 at bound
  rw [launch_from_original_force,offset]
  linarith only [bound]

theorem pulse_energy_conserved (time : ℝ) :
    energy coupledControl (pulsePath 0 time).body=energy coupledControl initialJoint := by
  have trace : (pulsePath 0 time).body.trace=1 := by
    rw [pulsePath,conjugation_trace,initial_joint_trace]
  rw [coupledControl,scalar_shift_energy _ _ _ trace,scalar_shift_energy _ _ _ initial_joint_trace]
  exact congrArg (fun e => e-offset) (pointer_control_conserved time initialJoint)

theorem source_quantum_equation (time : ℝ) :
    HasDerivAt (fun t => (pulsePath 0 t).body)
      (-Complex.I • (coupledControl*(pulsePath 0 time).body-(pulsePath 0 time).body*coupledControl)) time := by
  rw [coupledControl,scalar_shift_commutator]
  exact Port.source_quantum_equation 0 time

theorem release_balance : energy Pointer.baselineHamiltonian controlledJoint+released=
    energy coupledControl controlledJoint+launched := by
  simpa only [(switch_path_endpoints coupledControl Pointer.baselineHamiltonian).2,released,releasePath] using
    switch_path_conserved coupledControl Pointer.baselineHamiltonian controlledJoint launched 1

theorem released_is_original_gain : released=sourceOff 0 := by
  have original := source_off_balance 0
  have actual := release_balance
  rw [coupledControl,scalar_shift_energy _ _ _ controlled_joint_trace,launch_from_original_force] at actual
  linarith only [original,actual]

theorem released_positive : (7/5 : ℝ) < released := by
  rw [released_is_original_gain]
  simpa only [sub_zero] using source_momentum_gain_positive 0

theorem launch_path_nonnegative (s : ℝ) (lo : 0 ≤ s) : 0 ≤ launchPath s := by
  have shape : launchPath s=s*launched := by
    simp only [launchPath,launched,momentumPath,zero_add,one_mul]
  rw [shape]
  exact mul_nonneg lo (le_trans (by norm_num) launch_positive)

theorem release_path_positive (s : ℝ) (lo : 0 ≤ s) (hi : s ≤ 1) : 0 < releasePath s := by
  have shape : releasePath s=(1-s)*launched+s*released := by
    simp only [releasePath,released,momentumPath]
    ring
  have launch : 0 < launched := lt_of_lt_of_le (by norm_num) launch_positive
  have finish : 0 < released := lt_trans (by norm_num) released_positive
  rw [shape]
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) launch.le,mul_nonneg lo finish.le]

theorem zero_stock_output : (7/5 : ℝ) < kinetic released-kinetic 0 := by
  have positive : 0 < released := lt_trans (by norm_num) released_positive
  simpa only [kinetic,abs_of_pos positive,abs_zero,sub_zero] using released_positive

theorem total_energy_conserved : energy Pointer.baselineHamiltonian controlledJoint+kinetic released=
    energy Pointer.baselineHamiltonian initialJoint+kinetic 0 := by
  have launch := launch_balance
  have release := release_balance
  have pulse : energy coupledControl controlledJoint=energy coupledControl initialJoint := by
    have body : (pulsePath 0 (nativeClockStep : ℝ)).body=controlledJoint := by
      rw [pulsePath,controlledJoint]
    rw [← body]
    exact pulse_energy_conserved (nativeClockStep : ℝ)
  have positive : 0 < released := lt_trans (by norm_num) released_positive
  simp only [kinetic,abs_of_pos positive,abs_zero,add_zero]
  linarith only [launch,release,pulse]

theorem coupled_control_hermitian : coupledControl.IsHermitian := by
  rw [coupledControl]
  exact pointer_control_hermitian.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint offset from rfl))

theorem launch_integrates_force : launched-0=
    ∫ _x in (0 : ℝ)..1, force Pointer.baselineHamiltonian coupledControl initialJoint :=
  momentum_path_integral _ _ _ _

theorem release_integrates_force : released-launched=
    ∫ _x in (0 : ℝ)..1, force coupledControl Pointer.baselineHamiltonian controlledJoint :=
  momentum_path_integral _ _ _ _

def entry : ClockBody := ⟨initialJoint,0,0⟩

def plateau (time : ℝ) : ClockBody := ⟨(pulsePath 0 time).body,time,launched⟩

def outgoing (time : ℝ) : ClockBody := ⟨(Timeline.loadPath 0 time).body,time,released⟩

theorem entry_kinetic_zero : kinetic entry.momentum=0 := by simp [entry,kinetic]

theorem plateau_energy (time : ℝ) :
    energy coupledControl (plateau time).body+kinetic (plateau time).momentum=
      energy Pointer.baselineHamiltonian entry.body+kinetic entry.momentum := by
  have positive : 0 < launched := lt_of_lt_of_le (by norm_num) launch_positive
  simp only [plateau,pulse_energy_conserved,kinetic,abs_of_pos positive,entry,abs_zero,add_zero]
  exact launch_balance

theorem outgoing_energy (time : ℝ) :
    energy Pointer.baselineHamiltonian (outgoing time).body+kinetic (outgoing time).momentum=
      energy Pointer.baselineHamiltonian entry.body+kinetic entry.momentum := by
  simp only [outgoing,Timeline.loadPath,Timeline.load_energy_preserved,entry]
  exact total_energy_conserved

theorem outgoing_output (time : ℝ) :
    (7/5 : ℝ) < kinetic (outgoing time).momentum-kinetic entry.momentum := zero_stock_output

theorem plateau_clock (time : ℝ) : HasDerivAt (fun t => (plateau t).position) 1 time := hasDerivAt_id time

theorem plateau_momentum (time : ℝ) : HasDerivAt (fun t => (plateau t).momentum) 0 time := hasDerivAt_const time launched

theorem plateau_velocity (time : ℝ) :
    HasDerivAt (portHamiltonian coupledControl coupledControl (plateau time).body time) 1
      (plateau time).momentum :=
  canonical_velocity _ _ _ _ _ (lt_of_lt_of_le (by norm_num) launch_positive)

theorem launch_preserves_body : entry.body=(plateau 0).body := by
  change initialJoint=(pulsePath 0 0).body
  rw [pulse_body_flow,bodyFlow,Blocks.EnergyFrame.hamiltonianFlow]
  simp

theorem release_preserves_body : (plateau (nativeClockStep : ℝ)).body=(outgoing (nativeClockStep : ℝ)).body :=
  Timeline.jump_preserves_body 0

theorem original_extraction_projection :
    (plateau (nativeClockStep : ℝ)).body=(Runtime.readCurrent Runtime.afterFirst).joint := by
  change (pulsePath 0 (nativeClockStep : ℝ)).body=_
  have body : (pulsePath 0 (nativeClockStep : ℝ)).body=controlledJoint := by rw [pulsePath,controlledJoint]
  exact body.trans controlled_joint_exact

theorem original_load_projection :
    (outgoing (2*(nativeClockStep : ℝ))).body=(Runtime.readCurrent Runtime.afterSecond).joint := by
  have after : (nativeClockStep : ℝ) ≤ 2*(nativeClockStep : ℝ) := by linarith [nativeClock_small.1]
  have original := Timeline.at_next_load_clock 0
  rw [Timeline.atTime,if_neg (not_lt.mpr (nativeClock_small.1.le.trans after)),if_neg (not_lt.mpr after)] at original
  exact original

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.Launch
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
