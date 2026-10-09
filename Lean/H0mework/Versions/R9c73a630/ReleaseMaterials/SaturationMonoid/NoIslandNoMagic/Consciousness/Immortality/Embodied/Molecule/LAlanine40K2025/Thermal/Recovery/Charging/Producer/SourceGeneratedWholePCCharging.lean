import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Producer.SourceGeneratedChargingControl
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.HeldPCEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.WholeHamiltonianTrace

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Producer

open Collision Load.Source Load.Producer Load.Producer.RecoveryLedger
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source
open scoped Matrix ComplexOrder
noncomputable section

theorem chargedFirst_pc_energy_gt_one : 1 < pcEnergy chargedFirst.joint := by
  have lower := Maximum.charge_mean_lower Powered.Producer.poweredTotalHamiltonian (pcRead receivedState).joint
    Powered.Producer.poweredTotalHamiltonian_hermitian (pcRead receivedState).positive (pcRead receivedState).normalized
  rw [← chargedFirst_pc] at lower
  change Powered.Producer.poweredTotalHamiltonian.trace.re ≤
    Fintype.card PairController * pcEnergy chargedFirst.joint at lower
  have dimension : (0 : ℝ) ≤ Fintype.card PairController := Nat.cast_nonneg _
  nlinarith [Trace.source_pc_trace_gt_dimension]

theorem source_pc_energy_gain :
    (36 / 5 : ℝ) < pcEnergy chargedFirst.joint - pcEnergy receivedState.joint := by
  have previous := HeldEnergy.held_pc_energy_lt
  rw [← received_actual] at previous
  linarith [chargedFirst_pc_energy_gt_one]

theorem source_pc_capacity_gain :
    (36 / 5 : ℝ) < Powered.Producer.poweredJointCapacity (pcRead chargedFirst) -
      Powered.Producer.poweredJointCapacity (pcRead receivedState) := by
  change (36 / 5 : ℝ) < Powered.Producer.poweredJointCapacity (pcRead (chargeStep receivedState)) - _
  rw [chargeStep_capacity_balance]
  exact source_pc_energy_gain

theorem source_control_work_positive : (26 / 5 : ℝ) < sourceWork receivedState := by
  rw [chargeStep_actual_work]
  have environment := chargeStep_environment receivedState
  have lower := (abs_le.mp (HeldEnergy.boundary_energy_abs_le_one (chargeStep receivedState))).1
  have upper := (abs_le.mp (HeldEnergy.boundary_energy_abs_le_one receivedState)).2
  have gain := source_pc_energy_gain
  change (36 / 5 : ℝ) < pcEnergy (chargeStep receivedState).joint - pcEnergy receivedState.joint at gain
  simp only [totalEnergy, Load.Source.totalEnergy_split]
  linarith

theorem source_net_account_gain : (26 / 5 : ℝ) <
    loadBindingAccountedFreeEnergy chargedFirst - loadBindingAccountedFreeEnergy receivedState := by
  have paid := chargeStep_netAccount receivedState
  rw [chargeStep_entropy, sub_self, add_zero] at paid
  have positive := source_control_work_positive
  rw [← paid] at positive
  exact positive

theorem source_clock : chargedFirst.localClock = 5 * Propagation.Producer.nativeClockStep := by
  change (receivedState.localClock + Propagation.Producer.nativeClockStep) = _
  have inherited : receivedState.localClock = 4 * Propagation.Producer.nativeClockStep :=
    Recovery.Runtime.recoveryRuntime_firstClock
  rw [inherited]
  ring

theorem source_original_load_next :
    (loadStateNext chargedFirst).joint = loadAdvance (Propagation.Producer.nativeClockStep : ℝ) chargedFirst.joint :=
  loadStateNext_joint chargedFirst

theorem source_update_reflects_joint (left right : LoadState)
    (same : (chargeStep left).joint = (chargeStep right).joint) : left.joint = right.joint := by
  rw [chargeStep_joint, chargeStep_joint] at same
  exact Recovery.Producer.localConjugation_injective _ _ same

theorem sourceGeneratedWholePCCharging : type_of% received_actual ∧ type_of% sourceFlow_generated ∧
    type_of% source_pc_energy_gain ∧ type_of% source_pc_capacity_gain ∧
    type_of% source_control_work_positive ∧ type_of% source_net_account_gain ∧
    type_of% (chargeStep_joint receivedState) ∧ type_of% (chargeStep_entropy receivedState) ∧
    type_of% (chargeStep_environment receivedState) ∧ type_of% source_clock ∧ type_of% source_original_load_next ∧
    ∀ left right, (chargeStep left).joint = (chargeStep right).joint → left.joint = right.joint :=
  ⟨received_actual, sourceFlow_generated, source_pc_energy_gain, source_pc_capacity_gain,
    source_control_work_positive, source_net_account_gain, chargeStep_joint receivedState,
    chargeStep_entropy receivedState, chargeStep_environment receivedState, source_clock, source_original_load_next,
    source_update_reflects_joint⟩

end
end LAlanine40K2025.Thermal.Recovery.Charging.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
