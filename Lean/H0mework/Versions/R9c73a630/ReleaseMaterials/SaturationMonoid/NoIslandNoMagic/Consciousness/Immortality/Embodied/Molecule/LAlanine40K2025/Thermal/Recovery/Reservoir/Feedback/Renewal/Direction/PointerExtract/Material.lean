import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Control
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Port.Launch
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Collision Quantum Load.Producer.StrictThermal Propagation.Producer Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

attribute [local irreducible] flip controlHamiltonian coupledHamiltonian offset Pointer.baselineHamiltonian

def origin : Live.State := Extract.Runtime.readCurrent Extract.Runtime.afterFirst

structure Material where
  quantum : Live.State
  momentum : ℝ

def sourceEntry : Material := ⟨origin,0⟩

def quantumNext (current : Live.State) : Live.State :=
  ⟨current.localClock+nativeClockStep,pulse (nativeClockStep : ℝ)*current.action⟩

def onMomentum (current : Material) : ℝ :=
  Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian current.quantum.joint current.momentum 1

def advance (current : Material) : Material :=
  let target := quantumNext current.quantum
  ⟨target,Extract.Port.momentumPath coupledHamiltonian Pointer.baselineHamiltonian target.joint (onMomentum current) 1⟩

attribute [local irreducible] origin

theorem quantumNext_joint (current : Live.State) :
    (quantumNext current).joint=conjugation (pulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

theorem quantumNext_flip (current : Live.State) :
    (quantumNext current).joint=conjugation flip current.joint := by
  rw [quantumNext_joint,pulse_clock_density]

theorem next_body (current : Material) : bodyRead (advance current).quantum.joint=bodyRead current.quantum.joint := by
  change bodyRead (quantumNext current.quantum).joint=_
  rw [quantumNext_flip,flip_body]

theorem next_pointer_one (current : Material) : oneRead (advance current).quantum.joint=zeroRead current.quantum.joint := by
  change oneRead (quantumNext current.quantum).joint=_
  rw [quantumNext_flip,flip_one]

theorem next_pointer_zero (current : Material) : zeroRead (advance current).quantum.joint=oneRead current.quantum.joint := by
  change zeroRead (quantumNext current.quantum).joint=_
  rw [quantumNext_flip,flip_zero]

theorem on_balance (current : Material) :
    energy coupledHamiltonian current.quantum.joint+onMomentum current=
      energy Pointer.baselineHamiltonian current.quantum.joint+current.momentum := by
  simpa only [(Extract.Port.switch_path_endpoints Pointer.baselineHamiltonian coupledHamiltonian).2,onMomentum] using
    Extract.Port.switch_path_conserved Pointer.baselineHamiltonian coupledHamiltonian current.quantum.joint current.momentum 1

theorem off_balance (current : Material) :
    energy Pointer.baselineHamiltonian (advance current).quantum.joint+(advance current).momentum=
      energy coupledHamiltonian (advance current).quantum.joint+onMomentum current := by
  simpa only [(Extract.Port.switch_path_endpoints coupledHamiltonian Pointer.baselineHamiltonian).2,advance] using
    Extract.Port.switch_path_conserved coupledHamiltonian Pointer.baselineHamiltonian
      (quantumNext current.quantum).joint (onMomentum current) 1

theorem momentum_gain (current : Material) : (advance current).momentum-current.momentum=
    energy Pointer.baselineHamiltonian current.quantum.joint-energy Pointer.baselineHamiltonian (advance current).quantum.joint := by
  have first := on_balance current
  have last := off_balance current
  have hold : energy coupledHamiltonian (advance current).quantum.joint=energy coupledHamiltonian current.quantum.joint := by
    change energy coupledHamiltonian (quantumNext current.quantum).joint=_
    rw [quantumNext_joint,pulse_conserves]
  linarith only [first,last,hold]

private theorem zero_launch_lower {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H0 Hc rho : Matrix κ κ ℂ) (positive : rho.PosSemidef) (trace : rho.trace=1) :
    1 ≤ Extract.Port.momentumPath H0 (Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix κ κ ℂ)) rho 0 1 := by
  let shifted := Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix κ κ ℂ)
  have balance : energy shifted rho+Extract.Port.momentumPath H0 shifted rho 0 1=energy H0 rho+0 := by
    simpa only [(Extract.Port.switch_path_endpoints H0 shifted).2] using Extract.Port.switch_path_conserved H0 shifted rho 0 1
  dsimp only [shifted] at balance
  rw [Extract.Port.Launch.scalar_shift_energy _ _ _ trace] at balance
  have bound := Extract.Port.force_bound H0 Hc rho positive trace
  have force : Extract.Port.force H0 Hc rho=energy H0 rho-energy Hc rho := by
    simp only [Extract.Port.force,energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
    ring
  rw [force] at bound
  have lower := (abs_le.mp bound).1
  linarith only [lower,balance]

theorem on_source_lower : 1 ≤ onMomentum sourceEntry := by
  change 1 ≤ Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian sourceEntry.quantum.joint 0 1
  rw [coupledHamiltonian,offset]
  exact zero_launch_lower _ _ _ sourceEntry.quantum.positive sourceEntry.quantum.normalized

theorem source_momentum_positive : 0 < (advance sourceEntry).momentum := by
  have balance := momentum_gain sourceEntry
  change (advance sourceEntry).momentum-0=energy Pointer.baselineHamiltonian origin.joint-
    energy Pointer.baselineHamiltonian (quantumNext origin).joint at balance
  rw [quantumNext_flip] at balance
  have source : 0 < energy Pointer.baselineHamiltonian origin.joint-
      energy Pointer.baselineHamiltonian (conjugation flip origin.joint) := by
    rw [origin]
    exact current_flip_positive
  linarith only [balance,source]

theorem source_output : 0 < Extract.Port.kinetic (advance sourceEntry).momentum-Extract.Port.kinetic sourceEntry.momentum := by
  change 0 < |(advance sourceEntry).momentum|-|0|
  simpa only [abs_zero,sub_zero,abs_of_pos source_momentum_positive] using source_momentum_positive

theorem source_energy_conserved :
    Live.baselineEnergy (advance sourceEntry).quantum+Extract.Port.kinetic (advance sourceEntry).momentum=
      Live.baselineEnergy sourceEntry.quantum+Extract.Port.kinetic sourceEntry.momentum := by
  have balance := momentum_gain sourceEntry
  change energy Pointer.baselineHamiltonian (advance sourceEntry).quantum.joint+|(advance sourceEntry).momentum|=
    energy Pointer.baselineHamiltonian sourceEntry.quantum.joint+|0|
  rw [abs_of_pos source_momentum_positive,abs_zero]
  change (advance sourceEntry).momentum-0=_ at balance
  linarith only [balance]

theorem source_clock : (advance sourceEntry).quantum.localClock=13*nativeClockStep := by
  change origin.localClock+nativeClockStep=13*nativeClockStep
  have parent : origin.localClock=12*nativeClockStep := by
    rw [origin]
    exact Extract.Runtime.actual_clocks.2.1
  rw [parent]
  ring

theorem on_force_integral (current : Material) : onMomentum current-current.momentum=
    ∫ _x in (0 : ℝ)..1, Extract.Port.force Pointer.baselineHamiltonian coupledHamiltonian current.quantum.joint :=
  Extract.Port.momentum_path_integral _ _ _ _

theorem off_force_integral (current : Material) : (advance current).momentum-onMomentum current=
    ∫ _x in (0 : ℝ)..1, Extract.Port.force coupledHamiltonian Pointer.baselineHamiltonian (advance current).quantum.joint :=
  Extract.Port.momentum_path_integral _ _ _ _

def onPath (s : ℝ) : ℝ := Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian sourceEntry.quantum.joint 0 s

def offPath (s : ℝ) : ℝ := Extract.Port.momentumPath coupledHamiltonian Pointer.baselineHamiltonian
  (advance sourceEntry).quantum.joint (onMomentum sourceEntry) s

theorem on_path_nonnegative (s : ℝ) (lo : 0 ≤ s) : 0 ≤ onPath s := by
  have linear : onPath s=s*onMomentum sourceEntry := by
    simp only [onPath,onMomentum,Extract.Port.momentumPath,sourceEntry,zero_add,one_mul]
  rw [linear]
  exact mul_nonneg lo (le_trans (by norm_num) on_source_lower)

theorem off_path_positive (s : ℝ) (lo : 0 ≤ s) (hi : s ≤ 1) : 0 < offPath s := by
  have linear : offPath s=(1-s)*onMomentum sourceEntry+s*(advance sourceEntry).momentum := by
    simp only [offPath,advance,Extract.Port.momentumPath]
    ring
  have start : 0 < onMomentum sourceEntry := lt_of_lt_of_le (by norm_num) on_source_lower
  have finish := source_momentum_positive
  rw [linear]
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) start.le,mul_nonneg lo source_momentum_positive.le]

theorem next_load_branch (current : Material) :
    Resource.loadBlock (advance current).quantum=Resource.suppliedBlock current.quantum := by
  exact (congrArg (fun rho : PointerJoint => rho.toBlocks₁₁) (quantumNext_flip current.quantum)).trans
    (flip_left_block current.quantum.joint)

theorem next_supply_branch (current : Material) :
    Resource.suppliedBlock (advance current).quantum=Resource.loadBlock current.quantum := by
  exact (congrArg (fun rho : PointerJoint => rho.toBlocks₂₂) (quantumNext_flip current.quantum)).trans
    (flip_right_block current.quantum.joint)

theorem next_resources (current : Material) :
    Resource.values (advance current).quantum=Resource.values current.quantum := by
  simp only [Resource.values,next_body]

theorem source_pointer_payment :
    pointerEnergy (advance sourceEntry).quantum.joint+Extract.Port.kinetic (advance sourceEntry).momentum=
      pointerEnergy sourceEntry.quantum.joint := by
  have paid := momentum_gain sourceEntry
  change (advance sourceEntry).momentum-0=energy Pointer.baselineHamiltonian sourceEntry.quantum.joint-
    energy Pointer.baselineHamiltonian (quantumNext sourceEntry.quantum).joint at paid
  rw [quantumNext_flip,flip_baseline_work,sub_zero] at paid
  rw [pointerEnergy,next_pointer_one,Extract.Port.kinetic,abs_of_pos source_momentum_positive,paid,pointerEnergy]
  ring

theorem source_receiver_bound :
    Extract.Port.kinetic (advance sourceEntry).momentum ≤ pointerEnergy sourceEntry.quantum.joint := by
  have target : 0 ≤ pointerEnergy (advance sourceEntry).quantum.joint :=
    mul_nonneg (by norm_num) (oneRead_nonnegative _ (advance sourceEntry).quantum.positive)
  linarith only [source_pointer_payment,target]

theorem source_net_account :
    Live.freeEnergy (advance sourceEntry).quantum+Live.entropyProduction (advance sourceEntry).quantum+
      Extract.Port.kinetic (advance sourceEntry).momentum =
      Live.freeEnergy sourceEntry.quantum+Live.entropyProduction sourceEntry.quantum := by
  have first := Live.complete_account sourceEntry.quantum
  have last := Live.complete_account (advance sourceEntry).quantum
  have energy := source_energy_conserved
  change Live.baselineEnergy (advance sourceEntry).quantum+Extract.Port.kinetic (advance sourceEntry).momentum=
    Live.baselineEnergy sourceEntry.quantum+|0| at energy
  rw [abs_zero] at energy
  linarith only [first,last,energy]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
