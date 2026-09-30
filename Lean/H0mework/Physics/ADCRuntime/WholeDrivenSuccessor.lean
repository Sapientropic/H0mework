import H0mework.Physics.ADCRuntime.WholeRecordedReadout

/-! # Physical voltage readout and its own clock jointly generate the recipient next -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]

def receiverWholeHardwareProcessingTicks
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat)
    (technology downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) : Nat :=
  receiverWholeProcessingTicks hardware.adcCode counterBits technology
    (packetLineReadyTime technology (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig).value
    hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph

/-- Unclassified and rejected reads preserve their distinct outcomes; neither emits a drive. -/
def receiverWholeDrivenPhysicalNext?
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (counterBits lastTick : Nat) (technology : AIGCellTechnology)
    (inputInitial : BVBit → SIVolt)
    (initial : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (fits : current.val.sampleTick < 2 ^ counterBits) :
    Option (Option (FiniteADCPhysicalRuntimeCurrent hardware)) :=
  let ticks := receiverWholeHardwareProcessingTicks hardware counterBits technology downstreamTechnology downstreamGraph
  (receiverWholeRecordedRead counterBits lastTick technology inputInitial initial
    downstreamTechnology downstreamGraph current fits).map
      (Option.map fun received => startFiniteADCPhysicalRuntime hardware
        (finiteADCPhysicalDelayedEndpoint current ticks) (fun channel => !(received channel)))

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
variable (counterBits lastTick : Nat) (technology : AIGCellTechnology)
variable (inputInitial : BVBit → SIVolt)
variable (inputInitialRail : ∀ (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size) atom,
  (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls[node.val] = .atom atom →
    InRail (compilePacketLineDriver technology (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig atom)
      (inputInitial atom))
variable (initial : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig.decls.size → Bool → SIVolt)
variable (initialRail : ∀ node polarity,
  InRail (compileDualRailCell technology (aigOutputBank (receiverWholeGraph hardware.adcCode counterBits)).aig node polarity)
    (initial node polarity))
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCPhysicalRuntimeCurrent hardware) (fits : current.val.sampleTick < 2 ^ counterBits)
variable (inSchedule : current.val.sampleTick ≤ lastTick)

include inputInitialRail initialRail inSchedule

theorem receiverWholeDrivenPhysicalNext_generated :
    receiverWholeDrivenPhysicalNext? counterBits lastTick technology inputInitial initial
      downstreamTechnology downstreamGraph current fits =
        some (some (finiteADCPhysicalDelayedSuccessor
          (receiverWholeHardwareProcessingTicks hardware counterBits technology downstreamTechnology downstreamGraph) current)) := by
  unfold receiverWholeDrivenPhysicalNext?
  rw [receiverWholeRecordedRead_received counterBits lastTick technology inputInitial inputInitialRail
    initial initialRail downstreamTechnology downstreamGraph current fits inSchedule]
  simp only [Option.map_some, finiteADCPhysicalDelayedSuccessor, finiteADCPhysicalFeedback_exact]

/-- The generated recipient receives this run's actual switch state and regenerates its own sample. -/
theorem receiverWholeDrivenPhysicalNext_paid :
    ∃ next : FiniteADCPhysicalRuntimeCurrent hardware,
      receiverWholeDrivenPhysicalNext? counterBits lastTick technology inputInitial initial
        downstreamTechnology downstreamGraph current fits = some (some next) ∧
      finiteADCPhysicalStateAt next 0 =
        finiteADCPhysicalStateAt current (finiteADCPhysicalSwitchTimeAt current
          (receiverWholeHardwareProcessingTicks hardware counterBits technology downstreamTechnology downstreamGraph)) ∧
      next.val.sampleTick ≤ finiteADCPhysicalSuccessorTickBound hardware ∧
      SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
        (finiteADCPhysicalCurrentSource next) next.val.drive := by
  refine ⟨finiteADCPhysicalDelayedSuccessor
    (receiverWholeHardwareProcessingTicks hardware counterBits technology downstreamTechnology downstreamGraph) current,
    receiverWholeDrivenPhysicalNext_generated counterBits lastTick technology inputInitial inputInitialRail
      initial initialRail downstreamTechnology downstreamGraph current fits inSchedule, ?_, ?_, ?_⟩
  · exact finiteADCPhysicalDelayedSuccessor_no_reset _ current
  · exact finiteADCPhysicalDelayedSuccessor_sampleTick_le current _
  · exact finiteADCPhysicalDelayedSuccessor_regenerates_sample _ current

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
