import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.ExchangeComparison

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Source

open Collision Load.Source Load.Producer Load.Producer.RecoveryLedger Load.Producer.StrictThermal
open Work.Capacity Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def received : LoadState := Charging.Source.receivedState
def donor : Matrix PairController PairController ℂ :=
  Spectrum.reservoirState Powered.Producer.poweredTotalHamiltonian Powered.Producer.poweredTotalHamiltonian_hermitian

theorem donor_positive : donor.PosSemidef := Spectrum.spectralPure_positive _ _ _
theorem donor_trace : donor.trace = 1 := Spectrum.spectralPure_trace _ _ _

def pairOrigin : JointMatrix PairController := Matrix.kronecker (pcRead received).joint donor
def pairTarget : JointMatrix PairController :=
  Quantum.conjugation (Exchange.nearTransfer (nativeClockStep : ℝ)) pairOrigin
def pcTarget : Matrix PairController PairController ℂ := systemReduce pairTarget
def donorTarget : Matrix PairController PairController ℂ := bathReduce pairTarget

theorem pcTarget_positive : pcTarget.PosSemidef :=
  systemReduce_posSemidef _ (Quantum.conjugation_posSemidef _ _ ((pcRead received).positive.kronecker donor_positive))

theorem pcTarget_trace : pcTarget.trace = 1 := by
  rw [pcTarget, systemReduce_trace, pairTarget, Quantum.conjugation_trace, pairOrigin,
    Matrix.kronecker, Matrix.trace_kronecker, (pcRead received).normalized, donor_trace, one_mul]

theorem donor_energy_gt_one : 1 < energy Powered.Producer.poweredTotalHamiltonian donor := by
  have upper := Spectrum.energy_spectral_bounds Powered.Producer.poweredTotalHamiltonian
    (Charging.Maximum.chargedState Powered.Producer.poweredTotalHamiltonian donor
      Powered.Producer.poweredTotalHamiltonian_hermitian donor_positive.isHermitian)
    Powered.Producer.poweredTotalHamiltonian_hermitian
    (Quantum.conjugation_posSemidef _ _ donor_positive)
    ((Quantum.conjugation_trace _ _).trans donor_trace)
  have lower := Charging.Maximum.charge_mean_lower Powered.Producer.poweredTotalHamiltonian donor
    Powered.Producer.poweredTotalHamiltonian_hermitian donor_positive donor_trace
  have sourceTrace := Charging.Trace.source_pc_trace_gt_dimension
  have top : Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.firstIndex (ι := PairController)) =
      energy Powered.Producer.poweredTotalHamiltonian donor := (Spectrum.spectralPure_energy _ _ _).symm
  rw [top] at upper
  nlinarith [show (0 : ℝ) ≤ Fintype.card PairController from Nat.cast_nonneg _]

theorem donor_received_gap :
    (36 / 5 : ℝ) < energy Powered.Producer.poweredTotalHamiltonian donor -
      energy Powered.Producer.poweredTotalHamiltonian (pcRead received).joint := by
  have held := Charging.HeldEnergy.held_pc_energy_lt
  change pcEnergy Recovery.Producer.recoveryStateFirst.joint < -(31 / 5 : ℝ) at held
  change (36 / 5 : ℝ) < energy Powered.Producer.poweredTotalHamiltonian donor - pcEnergy received.joint
  change pcEnergy received.joint < -(31 / 5 : ℝ) at held
  linarith [donor_energy_gt_one]

theorem native_error_small : 1944 * (nativeClockStep : ℝ) < 6 / 5 := by
  rw [nativeClockStep_exact]
  norm_num

theorem pc_observable_error (O : Matrix PairController PairController ℂ) :
    |energy O pcTarget - energy O donor| ≤ 4 * ‖O‖ * (nativeClockStep : ℝ) := by
  have bound := Exchange.nearTransfer_read_error O (pcRead received).joint donor (pcRead received).positive
    (pcRead received).normalized donor_positive donor_trace (nativeClockStep : ℝ)
  rw [abs_of_pos nativeClock_small.1] at bound
  exact bound

theorem pc_energy_gain :
    6 < energy Powered.Producer.poweredTotalHamiltonian pcTarget -
      energy Powered.Producer.poweredTotalHamiltonian (pcRead received).joint := by
  have error := (abs_le.mp (pc_observable_error Powered.Producer.poweredTotalHamiltonian)).1
  have normH := poweredTotalHamiltonian_norm_le
  have q := nativeClock_small.1
  have small := native_error_small
  have gap := donor_received_gap
  nlinarith

def sourceExtraction : Matrix.unitaryGroup PairController ℂ :=
  Spectrum.extraction Powered.Producer.poweredTotalHamiltonian Powered.Producer.poweredTotalHamiltonian_hermitian

theorem pc_capacity_gain :
    6 < ergotropy Powered.Producer.poweredTotalHamiltonian pcTarget
      Powered.Producer.poweredTotalHamiltonian_hermitian pcTarget_positive.isHermitian -
      Powered.Producer.poweredJointCapacity (pcRead received) := by
  let O := Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) (star sourceExtraction)
    Powered.Producer.poweredTotalHamiltonian
  have read (state : Matrix PairController PairController ℂ) :
      energy O state = energy Powered.Producer.poweredTotalHamiltonian
        (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) sourceExtraction state) :=
    (energy_pullback _ _ _).symm
  have lower := (abs_le.mp (pc_observable_error Powered.Producer.poweredTotalHamiltonian)).1
  have upper := (abs_le.mp (pc_observable_error O)).2
  have normO : ‖O‖ = ‖Powered.Producer.poweredTotalHamiltonian‖ := conjugation_norm _ _
  rw [normO, read, read] at upper
  have extract := extractedWork_le_ergotropy Powered.Producer.poweredTotalHamiltonian pcTarget
    Powered.Producer.poweredTotalHamiltonian_hermitian pcTarget_positive.isHermitian sourceExtraction
  have margin := Spectrum.supplied_capacity_margin Powered.Producer.poweredTotalHamiltonian
    (pcRead received).joint Powered.Producer.poweredTotalHamiltonian_hermitian
    (pcRead received).positive (pcRead received).normalized
  change energy Powered.Producer.poweredTotalHamiltonian donor -
    energy Powered.Producer.poweredTotalHamiltonian (pcRead received).joint ≤
    (energy Powered.Producer.poweredTotalHamiltonian donor -
      energy Powered.Producer.poweredTotalHamiltonian
        (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) sourceExtraction donor)) -
        Powered.Producer.poweredJointCapacity (pcRead received) at margin
  have normH := poweredTotalHamiltonian_norm_le
  have q := nativeClock_small.1
  have small := native_error_small
  have gap := donor_received_gap
  nlinarith

theorem source_energy_balance :
    (energy Powered.Producer.poweredTotalHamiltonian pcTarget -
      energy Powered.Producer.poweredTotalHamiltonian (pcRead received).joint) +
    (energy Powered.Producer.poweredTotalHamiltonian donorTarget -
      energy Powered.Producer.poweredTotalHamiltonian donor) = 0 :=
  heatBalance _ _ _ _ _ (Real.cos_sq_add_sin_sq _) (pcRead received).normalized donor_trace

theorem donor_paid_gain : 6 < energy Powered.Producer.poweredTotalHamiltonian donor -
    energy Powered.Producer.poweredTotalHamiltonian donorTarget := by
  linarith [source_energy_balance, pc_energy_gain]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
