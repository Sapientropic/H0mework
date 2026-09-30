import H0mework.Computation.WholeReceiver.Physical
import H0mework.Physics.ADCRuntime.DelayedCounter

/-! # The whole graph's own physical read time drives the RLC endpoint clock -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]

def receiverWholeCaptureTime (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode) : SISecond :=
  aigInputSampledTime technology (aigOutputBank (receiverWholeGraph code counterBits)).aig
    inputReady clock clockCode

def receiverWholeReadTime (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) : SISecond :=
  aigInputSampledTime downstreamTechnology downstreamGraph
    (receiverWholeCaptureTime code counterBits technology inputReady clock clockCode).value clock clockCode

/-- Both ceilings use the physical source clock; no declaration-clock budget enters. -/
def receiverWholeProcessingTicks (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) : Nat :=
  finiteSamplingClockTickCount clock clockCode
    ⟨(receiverWholeCaptureTime code counterBits technology inputReady clock clockCode).value +
      (aigDualRailGraphDeadline downstreamTechnology downstreamGraph).value⟩

theorem receiverWholeReadTime_eq_processingTicks
    (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    (receiverWholeReadTime code counterBits technology inputReady clock clockCode
      downstreamTechnology downstreamGraph).value =
      (receiverWholeProcessingTicks code counterBits technology inputReady clock clockCode
        downstreamTechnology downstreamGraph : ℝ) *
          (finiteSamplingClockTickPeriod clock clockCode).value := rfl

theorem receiverWholeCaptureTime_le_readTime
    (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    (receiverWholeCaptureTime code counterBits technology inputReady clock clockCode).value ≤
      (receiverWholeReadTime code counterBits technology inputReady clock clockCode
        downstreamTechnology downstreamGraph).value := by
  have late := aigInputSampledTime_late downstreamTechnology downstreamGraph
    (receiverWholeCaptureTime code counterBits technology inputReady clock clockCode).value clock clockCode
  have delay := aigDualRailGraphDeadline_nonneg downstreamTechnology downstreamGraph
  dsimp only [receiverWholeReadTime]
  linarith

theorem receiverWholePhysicalSwitchTime_reads_actual_time
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (counterBits : Nat)
    (technology : AIGCellTechnology) (inputReady : ℝ)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    (finiteADCPhysicalSwitchTimeAt current
      (receiverWholeProcessingTicks hardware.adcCode counterBits technology inputReady
        hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph)).value =
      current.val.executedDuration.value +
        (receiverWholeReadTime hardware.adcCode counterBits technology inputReady
          hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph).value := by
  rw [finiteADCPhysicalSwitchTimeAt_value, receiverWholeReadTime_eq_processingTicks]
  have tickSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockTick current.property
  rw [tickSame]
  rfl

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
