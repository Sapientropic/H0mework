import H0mework.Physics.ReceiverActuation.CommonLoad
import H0mework.Computation.AIGHold.AIGBankRecoveryMemory

/-! # The whole bank's actual common load generates one recovered memory and one complete read -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def commonRecoverySampleTime : SISecond :=
  aigBankCommonRecoveryTime technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value hardware.meteredSource.fixture.coreSource hardware.clockCode

theorem commonRecoverySampleTime_nonnegative :
    0 ≤ (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value :=
  aigBankCommonRecoveryTime_nonneg _ _ _ _ _ _

def commonRecoveryStateAt
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size)
    (polarity : Bool) (time : ℝ) : SIVolt :=
  aigBankCommonRecoveryStateAt technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value node polarity time

def commonRecoveryMemory : AIGCapacitorMemory technology
    (aigOutputBank (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig :=
  aigBankCommonRecoveryMemory technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value hardware.meteredSource.fixture.coreSource hardware.clockCode
    (commonOutputRecoveryStart_nonnegative downstreamTechnology downstreamGraph)

theorem commonRecoveryMemory_exact
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size) (polarity : Bool) :
    (commonRecoveryMemory downstreamTechnology downstreamGraph current).gateInitial node polarity =
      commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value :=
  aigBankCommonRecoveryMemory_initial_exact _ _ _ _ _ _ _ _ _ _ _

theorem commonRecoveryMemory_restarts_without_reset (newAssignment : BVBit → Bool)
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size) (polarity : Bool) :
    aigMemoryStateAt technology (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
      (commonRecoveryMemory downstreamTechnology downstreamGraph current) newAssignment downstreamTechnology downstreamGraph
      hardware.meteredSource.fixture.coreSource hardware.clockCode node polarity 0 =
      commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value :=
  aigBankCommonRecoveryMemory_restart _ _ _ _ _ _ _ _ _ _ _ _ _ _

def commonRecoveryRead : Vector (Option Bool) 11 :=
  aigBankCommonRecoveryRead technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value hardware.meteredSource.fixture.coreSource hardware.clockCode

theorem commonRecoveryRead_is_complete_memory_projection :
    commonRecoveryRead downstreamTechnology downstreamGraph current =
      Vector.ofFn (fun index : Fin 11 =>
        let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
        railRead? (aigBankCell technology entry index)
          ((commonRecoveryMemory downstreamTechnology downstreamGraph current).gateInitial
            ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
              ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false)) := by
  apply Vector.ext
  intro index bound
  simp only [commonRecoveryRead, aigBankCommonRecoveryRead, Vector.getElem_ofFn,
    commonRecoveryMemory_exact, commonRecoveryStateAt, aigBankCommonRecoveryStateAt_output]
  rfl

theorem commonRecoveryRead_eq_source :
    commonRecoveryRead downstreamTechnology downstreamGraph current =
      (receiverWholeGraphRead (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
        (finiteADCRawAdmissionInputOfPacketFor hardware.adcCode
          (clockMax) current.packet)).map some := by
  rw [commonRecoveryRead, aigBankCommonRecoveryRead_eq_source_refs]
  apply Vector.ext
  intro index bounded
  simp only [Vector.getElem_ofFn, Vector.getElem_map]
  rw [receiverWholeGraphRead_get _ _ (⟨index, bounded⟩ : Fin 11)]
  rfl

theorem commonRecoveryRead_receives_actual_command :
    (receiverWholePhysicalDecode (commonRecoveryRead downstreamTechnology downstreamGraph current)).map
      (Option.map finiteADCRawBooleanReadout) = some (some current.plant.val.drive) := by
  rw [commonRecoveryRead_eq_source, receiverWholePhysicalDecode_map_some, Option.map_some]
  have decoded := receiverWholeDecode_eq_original hardware.adcCode
    (clockMax) current.packet
  rw [finiteADCRawMicroPacketResult_eq_receive hardware] at decoded
  have received := receive_recordedADCWirePacket_current current.plant current.fits
    (clockMax) current.inSchedule
  change receiveADC128WirePacket (finiteADCFixtureWithInitial hardware current.plant.val.initial)
    (clockMax) current.packet = some current.plant.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  rw [received] at decoded
  exact congrArg some decoded

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
