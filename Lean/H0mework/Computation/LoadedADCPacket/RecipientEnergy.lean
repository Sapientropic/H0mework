import H0mework.Computation.LoadedADCPacket.RecipientState
import H0mework.Physics.DrivenEnergy.StateCorrection
import H0mework.Computation.LoadedADCInformation.Account

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def decodedEnergy (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : SIJoule :=
  drivenRLCBankStoredEnergy
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (decodedRecipient packet)

def energyError (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) : SIJoule :=
  RLCStateError.correction
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (decodedRecipient current.packet) (voltageError current) (currentError current)

theorem recipient_energy (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration =
      decodedEnergy current.packet + energyError current := by
  have difference := RLCStateError.storedEnergy_difference
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (decodedRecipient current.packet) (voltageError current) (currentError current)
  rw [← endpoint_eq_shift current] at difference
  have values := congrArg (fun quantity : SIJoule => quantity.value) difference
  apply SIQuantity.ext
  change (finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration).value -
    (decodedEnergy current.packet).value = (energyError current).value at values
  change (finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration).value =
    (decodedEnergy current.packet).value + (energyError current).value
  linarith

theorem joint_energy (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    jointStoredEnergy current =
      current.memory.storedEnergy + decodedEnergy current.packet + energyError current := by
  rw [jointStoredEnergy, recipient_energy]
  apply SIQuantity.ext
  simp only [SIQuantity.add_value, add_assoc]

variable {β : Type} [DecidableEq β] [Hashable β]
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

theorem step_energy (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    ((loadedStep downstreamTechnology downstreamGraph current).memory.storedEnergy +
      decodedEnergy (loadedStep downstreamTechnology downstreamGraph current).packet +
      energyError (loadedStep downstreamTechnology downstreamGraph current)).value -
    (current.memory.storedEnergy + decodedEnergy current.packet + energyError current).value =
      (loadedStepWork downstreamTechnology downstreamGraph current).value -
        (loadedStepHeat downstreamTechnology downstreamGraph current).value := by
  have paid := loadedStep_energy_balance downstreamTechnology downstreamGraph current
  rw [joint_energy, joint_energy] at paid
  exact paid

variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem whole_material_energy (frames : Nat) :
    ((loadedAfter downstreamTechnology downstreamGraph seed frames).memory.storedEnergy +
      decodedEnergy (loadedAfter downstreamTechnology downstreamGraph seed frames).packet +
      energyError (loadedAfter downstreamTechnology downstreamGraph seed frames)).value -
    (seed.memory.storedEnergy + decodedEnergy seed.packet + energyError seed).value =
      workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) -
        heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  have paid := whole_material_account downstreamTechnology downstreamGraph seed frames
  rw [joint_energy, joint_energy] at paid
  exact paid

theorem material_heat_with_residual (frames : Nat) :
    heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ≤
      (seed.memory.storedEnergy + decodedEnergy seed.packet + energyError seed).value +
        workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  have paid := material_heat_budget downstreamTechnology downstreamGraph seed frames
  rw [joint_energy] at paid
  exact paid

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
