import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Consumers
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish
open Blocks.EnergyFrame
open Collision Quantum Resource Propagation.Producer Load.Source Load.Producer.StrictThermal Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def material : Material := Restore.Runtime.readCurrent Restore.Runtime.afterFirst
def origin : Live.State := material.quantum
theorem source_exact : material=Restore.output := rfl
theorem origin_joint : origin.joint=sourceEntry.quantum.joint := Restore.output_joint
theorem receiver_empty : material.momentum=0 := Restore.Runtime.actual_empty
theorem origin_clock : origin.localClock=14*nativeClockStep := Restore.Runtime.actual_clocks.2.1

def gap : ℝ := donorEnergyOf (suppliedBlock origin)-pcEnergyOf (suppliedBlock origin)

def groundProjector : Matrix PairController PairController ℂ :=
  Spectrum.spectralPure Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian Spectrum.lastIndex

theorem measured_energy_lower : -(244 : ℝ) ≤ measuredEnergy := by
  have pc := Blocks.energy_norm_mass Powered.Producer.poweredTotalHamiltonian
    (Load.Producer.RecoveryLedger.pcRead Reservoir.Source.received).joint
    (Load.Producer.RecoveryLedger.pcRead Reservoir.Source.received).positive
  rw [(Load.Producer.RecoveryLedger.pcRead Reservoir.Source.received).normalized,Complex.one_re,mul_one] at pc
  have pcLower := (abs_le.mp (pc.trans poweredTotalHamiltonian_norm_le)).1
  have environment := (Powered.Dynamics.controllerEnergy_range 2 (by norm_num)
    Reservoir.Source.received.joint Reservoir.Source.received.positive Reservoir.Source.received.normalized).1
  have boundary := (abs_le.mp (Charging.HeldEnergy.boundary_energy_abs_le_one Reservoir.Source.received)).1
  change -(243 : ℝ) ≤ Load.Source.pcEnergy Reservoir.Source.received.joint at pcLower
  change 0 ≤ Load.Source.environmentEnergy Reservoir.Source.received.joint at environment
  rw [measuredEnergy,Load.Source.totalEnergy_split]
  linarith only [pcLower,environment,boundary]

theorem origin_pointer_upper : oneRead origin.joint < (250001/500000 : ℝ) := by
  have actual : oneRead origin.joint=oneRead sourceTarget := by
    rw [origin_joint]
    exact current_pointer_memory
  rw [actual]
  have contrast := source_pointer_contrast
  have scale : (100000000 : ℝ) < measurementScale := Inverse.original_measurement_scale_lower
  have energy := measured_energy_lower
  by_contra bad
  have population : (250001/500000 : ℝ) ≤ oneRead sourceTarget := le_of_not_gt bad
  nlinarith only [contrast,scale,energy,population]

namespace Registered
def target : Live.State := respondNext origin
def execution : Live.State := Live.loadNext target
def transfer : ℝ := supplyTransfer origin
def netGain : ℝ := pcEnergyOf (bodyRead execution.joint)-pcEnergyOf (bodyRead origin.joint)

private theorem correlated_near_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (rho : JointMatrix ι) (positive : rho.PosSemidef) (epsilon : ℝ) :
    |energy H (Collision.systemReduce (conjugation (Exchange.nearTransfer epsilon) rho))-energy H (bathReduce rho)| ≤
      4*‖H‖*|epsilon| *rho.trace.re := by
  have bound := weighted_observable_error (Matrix.kronecker H 1) rho positive
    (Exchange.nearTransfer epsilon) Exchange.fullTransfer
  rw [Exchange.left_energy,Exchange.left_energy] at bound
  have full : energy H (Collision.systemReduce (conjugation Exchange.fullTransfer rho))=energy H (bathReduce rho) := by
    simpa only [Exchange.fullTransfer,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_pow (by decide : (2 : ℕ) ≠ 0),one_pow,zero_mul,one_mul,zero_add,add_zero,mul_zero] using
      exchange_energy H rho (Real.pi/2)
  rw [full] at bound
  have normH := NonUnitalStarAlgHom.norm_apply_le (Load.Producer.StrictThermal.tensorLeft (κ := ι)) H
  change ‖Matrix.kronecker H 1‖ ≤ ‖H‖ at normH
  have normU := Exchange.nearTransfer_error (ι := ι) epsilon
  have mass : 0 ≤ rho.trace.re := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  apply bound.trans
  calc
    _ ≤ 2*‖H‖*(2*|epsilon|)*rho.trace.re := by gcongr
    _ = _ := by ring

theorem transfer_error (current : Live.State) :
    |supplyTransfer current-(donorEnergyOf (suppliedBlock current)-pcEnergyOf (suppliedBlock current))| ≤
      4*‖Powered.Producer.poweredTotalHamiltonian‖*(nativeClockStep : ℝ)*(suppliedBlock current).trace.re := by
  have bound := correlated_near_error Powered.Producer.poweredTotalHamiltonian
    (Powered.Dynamics.systemReduce (suppliedBlock current))
    (Powered.Dynamics.systemReduce_posSemidef _ (suppliedBlock_positive current)) (nativeClockStep : ℝ)
  rw [abs_of_pos nativeClock_small.1,Powered.Dynamics.systemReduce_trace] at bound
  unfold supplyTransfer
  rw [suppliedBlock_next]
  unfold pcEnergyOf pcMatrixOf
  rw [supply_pair,native_pc_exchange,Native.sourceCoupling_clock]
  unfold donorEnergyOf donorMatrixOf
  have cancel (x y z : ℝ) : x-y-(z-y)=x-z := by ring
  rw [cancel]
  exact bound

theorem source_transfer_lower :
    gap-4*‖Powered.Producer.poweredTotalHamiltonian‖*(nativeClockStep : ℝ)*(suppliedBlock origin).trace.re ≤ transfer := by
  have bound := (abs_le.mp (transfer_error origin)).1
  change -(4*‖Powered.Producer.poweredTotalHamiltonian‖*(nativeClockStep : ℝ)*(suppliedBlock origin).trace.re) ≤ transfer-gap at bound
  linarith only [bound]

end Registered

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish
