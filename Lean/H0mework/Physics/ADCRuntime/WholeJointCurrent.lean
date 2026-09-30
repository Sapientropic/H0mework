import H0mework.Physics.ADCRuntime.WholeDrivenSuccessor
import H0mework.Computation.AIGHold.AIGMemoryEndpoint

/-! # A current owns its recorded plant occurrence and all actual receiver capacitors -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

structure FiniteADCWholeJointCurrent
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (clockMax : Nat) (technology : AIGCellTechnology) where
  plant : FiniteADCPhysicalRuntimeCurrent hardware
  inSchedule : plant.val.sampleTick ≤ clockMax
  memory : AIGCapacitorMemory technology (aigOutputBank
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig

noncomputable section

namespace FiniteADCWholeJointCurrent

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}

theorem fits (current : FiniteADCWholeJointCurrent hardware clockMax technology) :
    current.plant.val.sampleTick < 2 ^ (Nat.log 2 clockMax + 1) :=
  current.inSchedule.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)

def packet (current : FiniteADCWholeJointCurrent hardware clockMax technology) :
    FiniteADCWirePacketFor hardware.adcCode ((Nat.log 2 clockMax + 1)) :=
  recordedADCWirePacket hardware current.plant.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.plant.property) current.fits

def assignment (current : FiniteADCWholeJointCurrent hardware clockMax technology) : BVBit → Bool :=
  (finiteADCRawAdmissionAssignment (finiteADCRawAdmissionInputOfPacketFor hardware.adcCode
    (clockMax) current.packet)).toAIGAssignment

def physicalRead {β : Type} [DecidableEq β] [Hashable β]
    (current : FiniteADCWholeJointCurrent hardware clockMax technology)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    Option (Option FiniteBinaryDrive) :=
  receiverWholeRecordedRead ((Nat.log 2 clockMax + 1))
    (clockMax) technology current.memory.inputInitial
    current.memory.gateInitial downstreamTechnology downstreamGraph current.plant current.fits

theorem physicalRead_received {β : Type} [DecidableEq β] [Hashable β]
    (current : FiniteADCWholeJointCurrent hardware clockMax technology)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    current.physicalRead downstreamTechnology downstreamGraph = some (some current.plant.val.drive) := by
  exact receiverWholeRecordedRead_received ((Nat.log 2 clockMax + 1))
    (clockMax) technology current.memory.inputInitial
    (fun node atom registered => current.memory.inputInitial_in_rail atom node registered)
    current.memory.gateInitial current.memory.gateInitial_in_rail
    downstreamTechnology downstreamGraph current.plant current.fits current.inSchedule

end FiniteADCWholeJointCurrent

/-- Boot memory is the source state at the first recorded ADC snapshot. It is never reissued by a step. -/
def startFiniteADCWholeJointCurrent
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) (technology : AIGCellTechnology)
    (memory : AIGCapacitorMemory technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig)
    (drive : FiniteBinaryDrive) : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology where
  plant := startFiniteADCPhysicalRuntime hardware bootInitial drive
  inSchedule := finiteADCPhysicalBoot_sampleTick_le_runtimeMax hardware bootInitial drive
  memory := memory

def compileFiniteADCWholeJointBoot
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) (technology : AIGCellTechnology)
    (drive : FiniteBinaryDrive) : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology :=
  startFiniteADCWholeJointCurrent hardware bootInitial technology
    (AIGCapacitorMemory.zero technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode (finiteADCPhysicalRuntimeClockBits hardware bootInitial))).aig) drive

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
