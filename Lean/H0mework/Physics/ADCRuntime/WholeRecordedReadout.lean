import H0mework.Physics.ADCRuntime.WholeDrivenReadout

/-! # The actual RLC snapshot enters its source-driven whole receiver -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}

def receiverWholeRecordedRead (counterBits lastTick : Nat) (technology : AIGCellTechnology)
    (inputInitial : BVBit → SIVolt)
    (initial : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (fits : current.val.sampleTick < 2 ^ counterBits) :
    Option (Option FiniteBinaryDrive) :=
  let packet := recordedADCWirePacket hardware current.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.property) fits
  (receiverWholeDrivenRead hardware.adcCode counterBits
    (finiteADCRawAdmissionInputOfPacketFor hardware.adcCode lastTick packet) technology inputInitial initial
    hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph).map
      (Option.map finiteADCRawBooleanReadout)

theorem receiverWholeRecordedRead_received
    (counterBits lastTick : Nat) (technology : AIGCellTechnology)
    (inputInitial : BVBit → SIVolt)
    (inputInitialRail : ∀ (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls[node.val] = .atom atom →
        InRail (compilePacketLineDriver technology (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig atom)
          (inputInitial atom))
    (initial : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig node polarity)
        (initial node polarity))
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (fits : current.val.sampleTick < 2 ^ counterBits)
    (inSchedule : current.val.sampleTick ≤ lastTick) :
    receiverWholeRecordedRead counterBits lastTick technology inputInitial initial
      downstreamTechnology downstreamGraph current fits = some (some current.val.drive) := by
  let packet := recordedADCWirePacket hardware current.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.property) fits
  have actual := receiverWholeDrivenRead_eq_microExecute hardware.adcCode counterBits lastTick packet
    technology inputInitial inputInitialRail initial initialRail hardware.meteredSource.fixture.coreSource
    hardware.clockCode downstreamTechnology downstreamGraph
  rw [finiteADCRawMicroExecuteFor_completed, finiteADCRawMicroPacketResult_eq_receive] at actual
  have received := receive_recordedADCWirePacket_current current fits lastTick inSchedule
  change receiveADC128WirePacket (finiteADCFixtureWithInitial hardware current.val.initial)
    lastTick packet = some current.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  exact actual.trans (congrArg some received)

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
