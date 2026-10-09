import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Runtime.Consumers
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore
open Collision Quantum Load.Producer.StrictThermal Propagation.Producer Blocks.EnergyFrame Resource
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] flip controlHamiltonian coupledHamiltonian offset Pointer.baselineHamiltonian

def input : Material := Runtime.readCurrent Runtime.afterFirst
def output : Material := advance input

theorem input_actual : input=advance sourceEntry := rfl

private theorem flip_twice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : conjugation flip (conjugation flip rho)=rho := by
  rw [flip_conjugation,flip_conjugation]
  simp only [Matrix.toBlocks_fromBlocks₁₁,Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁,Matrix.toBlocks_fromBlocks₂₂,Matrix.fromBlocks_toBlocks]

theorem twice_joint (current : Material) : (advance (advance current)).quantum.joint=current.quantum.joint := by
  change (quantumNext (quantumNext current.quantum)).joint=_
  rw [quantumNext_flip,quantumNext_flip]
  exact flip_twice current.quantum.joint

theorem twice_momentum (current : Material) : (advance (advance current)).momentum=current.momentum := by
  have first := momentum_gain current
  have second := momentum_gain (advance current)
  rw [twice_joint] at second
  linarith only [first,second]

theorem output_joint : output.quantum.joint=sourceEntry.quantum.joint := twice_joint sourceEntry
theorem output_momentum : output.momentum=0 := twice_momentum sourceEntry
theorem input_positive : 0 < input.momentum := source_momentum_positive
theorem output_clock : output.quantum.localClock=14*nativeClockStep := by
  change (advance sourceEntry).quantum.localClock+nativeClockStep=_
  rw [source_clock]
  ring

theorem spent : Extract.Port.kinetic input.momentum-Extract.Port.kinetic output.momentum=
    Extract.Port.kinetic input.momentum := by
  simp only [output_momentum,Extract.Port.kinetic,abs_zero,sub_zero]

theorem positive_demand : 0 < Extract.Port.kinetic input.momentum-
    Extract.Port.kinetic output.momentum := by
  rw [spent,Extract.Port.kinetic,abs_of_pos input_positive]
  exact input_positive

theorem paid_energy : Live.baselineEnergy output.quantum+Extract.Port.kinetic output.momentum=
    Live.baselineEnergy input.quantum+Extract.Port.kinetic input.momentum := by
  have balance := momentum_gain input
  change energy Pointer.baselineHamiltonian output.quantum.joint+|output.momentum|=
    energy Pointer.baselineHamiltonian input.quantum.joint+|input.momentum|
  change output.momentum-input.momentum=energy Pointer.baselineHamiltonian input.quantum.joint-
    energy Pointer.baselineHamiltonian output.quantum.joint at balance
  rw [output_momentum,abs_zero,abs_of_pos input_positive]
  rw [output_momentum] at balance
  linarith only [balance]

theorem pointer_recharged : pointerEnergy output.quantum.joint-pointerEnergy input.quantum.joint=
    Extract.Port.kinetic input.momentum := by
  rw [output_joint]
  have balance := source_pointer_payment
  change pointerEnergy input.quantum.joint+Extract.Port.kinetic input.momentum=
    pointerEnergy sourceEntry.quantum.joint at balance
  linarith only [balance]

theorem pointer_recharge_positive : 0 < pointerEnergy output.quantum.joint-pointerEnergy input.quantum.joint := by
  rw [pointer_recharged,Extract.Port.kinetic,abs_of_pos input_positive]
  exact input_positive

theorem actual_change : output.quantum.joint ≠ input.quantum.joint := by
  intro same
  have demand := pointer_recharge_positive
  rw [same,sub_self] at demand
  exact (lt_irrefl 0) demand

theorem output_body : bodyRead output.quantum.joint=bodyRead input.quantum.joint := next_body input
theorem output_resources : values output.quantum=values input.quantum := next_resources input
theorem output_branches : loadBlock output.quantum=loadBlock sourceEntry.quantum ∧
    suppliedBlock output.quantum=suppliedBlock sourceEntry.quantum := by
  exact ⟨(next_load_branch input).trans (next_supply_branch sourceEntry),
    (next_supply_branch input).trans (next_load_branch sourceEntry)⟩

theorem output_memory : oneRead output.quantum.joint=oneRead sourceEntry.quantum.joint := by
  rw [output_joint]

theorem paid_net_account : Live.freeEnergy output.quantum+Live.entropyProduction output.quantum+
    Extract.Port.kinetic output.momentum=
    Live.freeEnergy input.quantum+Live.entropyProduction input.quantum+Extract.Port.kinetic input.momentum := by
  have before := Live.complete_account input.quantum
  have after := Live.complete_account output.quantum
  linarith only [before,after,paid_energy]

private theorem shifted_launch_lower {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H0 Hc rho : Matrix κ κ ℂ) (positive : rho.PosSemidef) (trace : rho.trace=1) (p : ℝ) :
    p+1 ≤ Extract.Port.momentumPath H0 (Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix κ κ ℂ)) rho p 1 := by
  let shifted := Hc-(‖H0‖+‖Hc‖+1) • (1 : Matrix κ κ ℂ)
  have balance : energy shifted rho+Extract.Port.momentumPath H0 shifted rho p 1=energy H0 rho+p := by
    simpa only [(Extract.Port.switch_path_endpoints H0 shifted).2] using Extract.Port.switch_path_conserved H0 shifted rho p 1
  dsimp only [shifted] at balance
  rw [Extract.Port.Launch.scalar_shift_energy _ _ _ trace] at balance
  have bound := Extract.Port.force_bound H0 Hc rho positive trace
  have force : Extract.Port.force H0 Hc rho=energy H0 rho-energy Hc rho := by
    simp only [Extract.Port.force,energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
    ring
  rw [force] at bound
  have lower := (abs_le.mp bound).1
  linarith only [balance,lower]

theorem launch_lower (current : Material) : current.momentum+1 ≤ onMomentum current := by
  change current.momentum+1 ≤ Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian current.quantum.joint current.momentum 1
  rw [coupledHamiltonian,offset]
  exact shifted_launch_lower _ _ _ current.quantum.positive current.quantum.normalized _

def onPath (s : ℝ) : ℝ := Extract.Port.momentumPath Pointer.baselineHamiltonian coupledHamiltonian
  input.quantum.joint input.momentum s
def offPath (s : ℝ) : ℝ := Extract.Port.momentumPath coupledHamiltonian Pointer.baselineHamiltonian
  output.quantum.joint (onMomentum input) s

theorem on_positive (s : ℝ) (lo : 0 ≤ s) : 0 < onPath s := by
  have linear : onPath s=input.momentum+s*(onMomentum input-input.momentum) := by
    simp only [onPath,onMomentum,Extract.Port.momentumPath,one_mul]
    ring
  rw [linear]
  have lower := launch_lower input
  have paid := input_positive
  nlinarith [mul_nonneg lo (show 0 ≤ onMomentum input-input.momentum by linarith only [lower])]

theorem off_nonnegative (s : ℝ) (hi : s ≤ 1) : 0 ≤ offPath s := by
  have linear : offPath s=(1-s)*onMomentum input+s*output.momentum := by
    simp only [offPath,output,advance,Extract.Port.momentumPath]
    ring
  rw [linear,output_momentum,mul_zero,add_zero]
  exact mul_nonneg (sub_nonneg.mpr hi) (le_trans (by linarith only [input_positive]) (launch_lower input))

theorem on_force : onMomentum input-input.momentum=
    ∫ _s in (0 : ℝ)..1, Extract.Port.force Pointer.baselineHamiltonian coupledHamiltonian input.quantum.joint :=
  on_force_integral input
theorem off_force : output.momentum-onMomentum input=
    ∫ _s in (0 : ℝ)..1, Extract.Port.force coupledHamiltonian Pointer.baselineHamiltonian output.quantum.joint :=
  off_force_integral input

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore
