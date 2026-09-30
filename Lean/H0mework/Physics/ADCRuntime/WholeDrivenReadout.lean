import H0mework.Physics.ADCRuntime.WholePhysicalClock
import H0mework.Physics.ConductanceCell.PacketLineDriver

/-! # Raw packet bits generate their own analog drivers and complete physical readout -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]

def receiverWholeDrivenRead (code : FiniteADCResolutionCode) (counterBits : Nat)
    (raw : FiniteADCRawAdmissionInput code counterBits) (technology : AIGCellTechnology)
    (inputInitial : BVBit → SIVolt)
    (initial : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size → Bool → SIVolt)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    Option (Option (Vector Bool 10)) :=
  let graph := (aigOutputBank (receiverWholeGraph code counterBits)).aig
  let input := packetLineInputWave technology graph
    (finiteADCRawAdmissionAssignment raw).toAIGAssignment inputInitial
  receiverWholePhysicalDecode (aigBankHeldRead technology (receiverWholeGraph code counterBits)
    input initial downstreamTechnology downstreamGraph (packetLineReadyTime technology graph).value clock clockCode)

theorem receiverWholeDrivenRead_eq_microExecute
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (technology : AIGCellTechnology)
    (inputInitial : BVBit → SIVolt)
    (inputInitialRail : ∀ (node : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls[node.val] = .atom atom →
        InRail (compilePacketLineDriver technology (aigOutputBank (receiverWholeGraph code counterBits)).aig atom)
          (inputInitial atom))
    (initial : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank (receiverWholeGraph code counterBits)).aig node polarity)
        (initial node polarity))
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    (receiverWholeDrivenRead code counterBits (finiteADCRawAdmissionInputOfPacketFor code lastTick packet)
      technology inputInitial initial clock clockCode downstreamTechnology downstreamGraph).map
        (Option.map finiteADCRawBooleanReadout) =
        finiteADCRawMicroOutput (finiteADCRawMicroExecuteFor code lastTick packet) := by
  let graph := (aigOutputBank (receiverWholeGraph code counterBits)).aig
  let raw := finiteADCRawAdmissionInputOfPacketFor code lastTick packet
  let first := (packetLineReadyTime technology graph).value
  let last := (receiverWholeCaptureTime code counterBits technology first clock clockCode).value
  have inputs := packetLineInputWave_registered_consumers technology graph
    (finiteADCRawAdmissionAssignment raw).toAIGAssignment inputInitial inputInitialRail last
  exact receiverWholePhysical_eq_microExecute code counterBits lastTick packet technology
    (packetLineInputWave technology graph (finiteADCRawAdmissionAssignment raw).toAIGAssignment inputInitial)
    initial initialRail inputs.1 first last (packetLineReadyTime_nonneg technology graph) inputs.2
    clock clockCode le_rfl downstreamTechnology downstreamGraph

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
