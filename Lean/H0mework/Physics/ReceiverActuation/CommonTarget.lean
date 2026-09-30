import H0mework.Physics.ReceiverActuation.CommonRecovery
import H0mework.Physics.ReceiverActuation.CommonRecipient

/-! # One recovered physical target owns the complete capacitor memory and every recipient row -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def commonRecoveryTarget :
    AIGCapacitorMemory technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig ×
      FiniteDimensionedSeriesRLCPortState :=
  (commonRecoveryMemory downstreamTechnology downstreamGraph current,
    commonRecipientRecoveryAt downstreamTechnology downstreamGraph current
      (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value)

def commonRecoveryTargetRead : Option (Option FiniteBinaryDrive) :=
  let target := commonRecoveryTarget downstreamTechnology downstreamGraph current
  let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
  (receiverWholePhysicalDecode (Vector.ofFn fun index : Fin 11 =>
    railRead? (aigBankCell technology entry index)
      (target.1.gateInitial ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false))).map (Option.map finiteADCRawBooleanReadout)

theorem commonRecoveryTarget_reads_actual_command :
    commonRecoveryTargetRead downstreamTechnology downstreamGraph current = some (some current.plant.val.drive) := by
  have actual := commonRecoveryRead_receives_actual_command downstreamTechnology downstreamGraph current
  rw [commonRecoveryRead_is_complete_memory_projection] at actual
  exact actual

theorem commonRecoveryTarget_memory_exact
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size) (polarity : Bool) :
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.gateInitial node polarity =
      commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value :=
  commonRecoveryMemory_exact _ _ _ _ _

theorem commonRecoveryTarget_recipient_exact :
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 =
      commonRecipientRecoveryAt downstreamTechnology downstreamGraph current
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value := rfl

def commonRecoveryTargetPortVoltage (channel : FiniteEmbodimentChannel) : SIVolt :=
  let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
  let index := outputLoadPort channel
  (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.gateInitial
    ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
      ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false

theorem commonRecoveryTargetPortVoltage_in_rail (channel : FiniteEmbodimentChannel) :
    InRail (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel)
      (commonRecoveryTargetPortVoltage downstreamTechnology downstreamGraph current channel) :=
  (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.gateInitial_in_rail _ _

def commonRecoveryTargetEnergy (channel : FiniteEmbodimentChannel) : SIJoule :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
  let recipient := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
  ⟨cell.capacitance.value / 2 * (commonRecoveryTargetPortVoltage downstreamTechnology downstreamGraph current channel).value ^ 2 +
    (run.capacitanceAt channel).value / 2 * (recipient.voltageAt channel).value ^ 2 +
    (run.inductanceAt channel).value / 2 * (recipient.currentAt channel).value ^ 2⟩

theorem commonRecoveryTargetEnergy_bound (channel : FiniteEmbodimentChannel) :
    (commonRecoveryTargetEnergy downstreamTechnology downstreamGraph current channel).value ≤
      (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value / 2 +
        (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel).capacitance.value / 2 *
        (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel).supply.value ^ 2 := by
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  have rail := commonRecoveryTargetPortVoltage_in_rail downstreamTechnology downstreamGraph current channel
  have square := (sq_le_sq₀ rail.1 cell.supply_pos.le).mpr rail.2
  have capacitor := mul_le_mul_of_nonneg_left square (div_nonneg cell.capacitance_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have recipient := commonRecipientRecoveryEnergyAt_le_original_half downstreamTechnology downstreamGraph current channel
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
    (commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current)
  rw [commonRecipientRecoveryEnergyAt_eq_physical] at recipient
  dsimp only [commonRecoveryTargetEnergy, commonRecoveryTarget] at *
  dsimp only [cell] at capacitor
  linarith

/-- The next load consumes the literal recovered U,V,I of this common target. -/
def commonRecoveryTargetReloadAt (channel : FiniteEmbodimentChannel) (time : ℝ) : Fin 3 → ℝ :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
  let recipient := (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
  capacitorRLCStateAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel
    (commonRecoveryTargetPortVoltage downstreamTechnology downstreamGraph current channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time

theorem commonRecoveryTargetReloadAt_initial (channel : FiniteEmbodimentChannel) :
    commonRecoveryTargetReloadAt downstreamTechnology downstreamGraph current channel 0 =
      capacitorRLCInitial (commonRecoveryTargetPortVoltage downstreamTechnology downstreamGraph current channel)
        ((commonRecoveryTarget downstreamTechnology downstreamGraph current).2.voltageAt channel)
        ((commonRecoveryTarget downstreamTechnology downstreamGraph current).2.currentAt channel) :=
  capacitorRLCStateAt_initial _ _ _ _ _ _ _

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
