import H0mework.Computation.AIGHold.AIGBankRecovery
import H0mework.Physics.ReceiverActuation.OutputLoad
import H0mework.Physics.ReceiverActuation.LoadedCapacitorRecovery

/-! # The same whole receiver restores its loaded output with its original running controls -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def outputRecoveryLoadDuration (channel : FiniteEmbodimentChannel) : SISecond :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  loadedCapacitorDuration cell
    (compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode)
    hardware.meteredSource.fixture.coreSource hardware.clockCode channel

def outputRecoveryStartTime (channel : FiniteEmbodimentChannel) : SISecond :=
  ⟨(readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value +
      (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph channel).value⟩

variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def outputRecoveryInitialVoltage (channel : FiniteEmbodimentChannel) : SIVolt :=
  ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel
    (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value 0⟩

def outputRecoveryControl (channel : FiniteEmbodimentChannel) (time : ℝ) : SIVolt :=
  aigBankRecoveryControl technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) current.memory current.assignment
    (outputLoadPort channel)
    (outputRecoveryStartTime (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value time

theorem outputRecoveryControl_is_original_negative (channel : FiniteEmbodimentChannel) (time : ℝ) :
    outputRecoveryControl downstreamTechnology downstreamGraph current channel time =
      let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
      let index := outputLoadPort channel
      current.receiverStateAt downstreamTechnology downstreamGraph
        ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
          ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ true
        ((outputRecoveryStartTime (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph channel).value + time) := by
  simp only [outputRecoveryControl, aigBankRecoveryControl, receiverStateAt, aigMemoryStateAt,
    aigHeldBankStateAt, Bool.true_eq_false, and_false, ↓reduceDIte]

def outputRecoveryVoltageAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIVolt :=
  aigBankRecoveryVoltageAt technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) current.memory current.assignment
    (outputLoadPort channel) (outputRecoveryInitialVoltage downstreamTechnology downstreamGraph current channel)
    (outputRecoveryStartTime (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value time

theorem outputRecoveryVoltageAt_initial (channel : FiniteEmbodimentChannel) :
    outputRecoveryVoltageAt downstreamTechnology downstreamGraph current channel 0 =
      ⟨current.outputLoadStateAt downstreamTechnology downstreamGraph channel
        (outputRecoveryLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph channel).value 0⟩ :=
  aigBankRecoveryVoltageAt_initial _ _ _ _ _ _ _

def outputRecoverySampleTime (channel : FiniteEmbodimentChannel) : SISecond :=
  aigBankRecoverySampleTime technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) (outputLoadPort channel)
    (outputRecoveryInitialVoltage downstreamTechnology downstreamGraph current channel)
    (outputRecoveryStartTime (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value hardware.meteredSource.fixture.coreSource hardware.clockCode

theorem outputCommand_is_recorded_drive (channel : FiniteEmbodimentChannel) :
    AIG.denote current.assignment
      ⟨(receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))).aig,
        (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))).vec.get
          (outputLoadPort channel).val (outputLoadPort channel).isLt⟩ = current.plant.val.drive channel := by
  let input := finiteADCRawAdmissionInputOfPacketFor hardware.adcCode
    (clockMax) current.packet
  have decoded := receiverWholeDecode_eq_original hardware.adcCode
    (clockMax) current.packet
  rw [finiteADCRawMicroPacketResult_eq_receive hardware] at decoded
  have received := receive_recordedADCWirePacket_current current.plant current.fits
    (clockMax) current.inSchedule
  change receiveADC128WirePacket (finiteADCFixtureWithInitial hardware current.plant.val.initial)
    (clockMax) current.packet = some current.plant.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  rw [received] at decoded
  change (receiverWholeDecode (receiverWholeGraphRead
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) input)).map
      finiteADCRawBooleanReadout = some current.plant.val.drive at decoded
  unfold receiverWholeDecode at decoded
  split at decoded
  · simp only [Option.map_some, Option.some.injEq] at decoded
    have result := congrFun decoded channel
    simp only [finiteADCRawBooleanReadout, Vector.getElem_ofFn] at result
    have graphRead := receiverWholeGraphRead_get
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) input (outputLoadPort channel)
    exact graphRead.symm.trans result
  · simp only [Option.map_none, reduceCtorEq] at decoded

/-- The recorded packet and actual graph history pay all recovery-control bands. -/
theorem outputRecoverySampleTime_restores_own_command (channel : FiniteEmbodimentChannel) :
    BitBand (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel)
      (current.plant.val.drive channel)
      (outputRecoveryVoltageAt downstreamTechnology downstreamGraph current channel
        (outputRecoverySampleTime downstreamTechnology downstreamGraph current channel).value) := by
  have restored := aigBankRecoverySampleTime_correct technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))) current.memory current.assignment
    (outputLoadPort channel) (outputRecoveryInitialVoltage downstreamTechnology downstreamGraph current channel)
    (outputRecoveryStartTime (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph channel).value hardware.meteredSource.fixture.coreSource hardware.clockCode
  rw [current.outputCommand_is_recorded_drive channel] at restored
  exact restored

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
