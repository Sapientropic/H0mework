import H0mework.Physics.ADCRuntime.WholeJointCurrent
import H0mework.Computation.AIGHold.AIGHeldStateReadout

/-! # One immutable clock maximum indexes the actual receiver read and capacitor history -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def readDelay : SISecond :=
  receiverWholeReadTime hardware.adcCode ((Nat.log 2 clockMax + 1)) technology
    (packetLineReadyTime technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig).value
    hardware.meteredSource.fixture.coreSource hardware.clockCode downstreamTechnology downstreamGraph

theorem readDelay_nonneg : 0 ≤ (readDelay (hardware := hardware) (clockMax := clockMax)
    (technology := technology) downstreamTechnology downstreamGraph).value := by
  unfold readDelay
  rw [receiverWholeReadTime_eq_processingTicks]
  exact mul_nonneg (Nat.cast_nonneg _) (finiteSamplingClockTickPeriod_pos
    hardware.meteredSource.fixture.coreSource hardware.clockCode).le

def receiverStateAt :
    Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size → Bool → ℝ → SIVolt :=
  aigMemoryStateAt technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    current.memory current.assignment downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode

theorem physicalRead_is_state_projection :
    let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
    current.physicalRead downstreamTechnology downstreamGraph =
      (receiverWholePhysicalDecode (Vector.ofFn fun index : Fin 11 =>
        railRead? (aigBankCell technology entry index)
          (current.receiverStateAt downstreamTechnology downstreamGraph
            ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
              ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false
            (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
              downstreamTechnology downstreamGraph).value))).map (Option.map finiteADCRawBooleanReadout) := by
  exact congrArg (fun readings => (receiverWholePhysicalDecode readings).map
    (Option.map finiteADCRawBooleanReadout))
    (aigBankHeldRead_eq_state_projection technology
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
      (aigMemoryInputWave technology
        (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
        current.memory current.assignment)
      current.memory.gateInitial downstreamTechnology downstreamGraph
      (packetLineReadyTime technology (aigOutputBank
        (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig).value
      hardware.meteredSource.fixture.coreSource hardware.clockCode)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
