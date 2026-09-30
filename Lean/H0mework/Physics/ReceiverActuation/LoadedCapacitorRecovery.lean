import H0mework.Physics.ReceiverActuation.StrictContraction
import H0mework.Physics.ConductanceCell.ArbitraryRecovery
import H0mework.Physics.ConductanceCell.DrivenEnergy
import H0mework.Physics.RLCResponse.SourceCoupling

/-! # The same loaded capacitor enters actual renewal, never a replacement boot state -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface Cells.Conductance Cells.Storage Set

noncomputable section

variable (cell : LoadedConductanceCellSource) (hold : ClockedLeakyHoldSource cell)
  (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode) (channel : FiniteEmbodimentChannel)

def loadedCapacitorDuration : SISecond :=
  finiteSamplingClockSampleTime clock clockCode
    (capacitorRLCHalfEnergyWait cell hold (resonantDrivenCoreDimensionedSource clock) channel)

theorem loadedCapacitorDuration_pos : 0 < (loadedCapacitorDuration cell hold clock clockCode channel).value :=
  lt_of_lt_of_le (capacitorRLCHalfEnergyWait_pos cell hold (resonantDrivenCoreDimensionedSource clock) channel)
    (finiteSamplingClock_requested_le_sampleTime clock clockCode _)

variable (holdInitial voltageInitial : SIVolt) (currentInitial : SIAmpere)

def loadedCapacitorEndVoltage : SIVolt :=
  ⟨capacitorRLCStateAt cell hold (resonantDrivenCoreDimensionedSource clock) channel
    holdInitial voltageInitial currentInitial (loadedCapacitorDuration cell hold clock clockCode channel).value 0⟩

theorem loadedCapacitorDuration_pays_half_energy :
    (capacitorRLCEnergyAt cell hold (resonantDrivenCoreDimensionedSource clock) channel holdInitial voltageInitial currentInitial
      (loadedCapacitorDuration cell hold clock clockCode channel).value).value ≤
      (capacitorRLCEnergyAt cell hold (resonantDrivenCoreDimensionedSource clock) channel holdInitial voltageInitial currentInitial 0).value / 2 :=
  capacitorRLCEnergyAt_le_half cell hold (resonantDrivenCoreDimensionedSource clock) channel
    holdInitial voltageInitial currentInitial _ (finiteSamplingClock_requested_le_sampleTime clock clockCode _)

def loadedCapacitorRecoveryVoltageAt (left right : ℝ → SIVolt) (time : ℝ) : SIVolt :=
  ⟨cell.drivenVoltageAt left right
    (loadedCapacitorEndVoltage cell hold clock clockCode channel holdInitial voltageInitial currentInitial) time⟩

theorem loadedCapacitorRecoveryVoltageAt_initial (left right : ℝ → SIVolt) :
    loadedCapacitorRecoveryVoltageAt cell hold clock clockCode channel holdInitial voltageInitial currentInitial left right 0 =
      loadedCapacitorEndVoltage cell hold clock clockCode channel holdInitial voltageInitial currentInitial := by
  apply SIQuantity.ext
  exact cell.drivenVoltageAt_initial _ _ _

def loadedCapacitorRecoveryEnergyAt (left right : ℝ → SIVolt) (time : ℝ) : SIJoule :=
  cell.drivenStoredEnergyAt left right
    (loadedCapacitorEndVoltage cell hold clock clockCode channel holdInitial voltageInitial currentInitial) time

theorem loadedCapacitorRecoveryEnergyAt_initial (left right : ℝ → SIVolt) :
    (loadedCapacitorRecoveryEnergyAt cell hold clock clockCode channel holdInitial voltageInitial currentInitial left right 0).value =
      (capacitorRLCHoldEnergyAt cell hold (resonantDrivenCoreDimensionedSource clock) channel
        holdInitial voltageInitial currentInitial (loadedCapacitorDuration cell hold clock clockCode channel).value).value := by
  exact cell.drivenStoredEnergyAt_initial _ _ _

theorem loadedCapacitorRecoveryEnergyAt_power_balance
    (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) :
    HasDerivAt
      (fun t => (loadedCapacitorRecoveryEnergyAt cell hold clock clockCode channel
        holdInitial voltageInitial currentInitial left right t).value)
      ((cell.supplyPower (left time) (right time)
          (loadedCapacitorRecoveryVoltageAt cell hold clock clockCode channel holdInitial voltageInitial currentInitial left right time)).value -
        (cell.dissipatedPower (left time) (right time)
          (loadedCapacitorRecoveryVoltageAt cell hold clock clockCode channel holdInitial voltageInitial currentInitial left right time)).value) time :=
  cell.drivenStoredEnergyAt_power_balance left right _ leftContinuous rightContinuous time

def loadedCapacitorRecoverySampleTime (first : ℝ) : SISecond :=
  finiteSamplingClockSampleTime clock clockCode
    ⟨first + (cell.arbitraryRecoveryTime
      (loadedCapacitorEndVoltage cell hold clock clockCode channel holdInitial voltageInitial currentInitial)).value⟩

theorem loadedCapacitorRecoverySampleTime_reestablishes_bit
    (leftBit rightBit : Bool) (left right : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (first : ℝ) (firstNonnegative : 0 ≤ first)
    (stable : ∀ t ∈ Icc first
        (loadedCapacitorRecoverySampleTime cell hold clock clockCode channel holdInitial voltageInitial currentInitial first).value,
      BitBand cell leftBit (left t) ∧ BitBand cell rightBit (right t)) :
    BitBand cell (!(leftBit && rightBit))
      (loadedCapacitorRecoveryVoltageAt cell hold clock clockCode channel holdInitial voltageInitial currentInitial
        left right
        (loadedCapacitorRecoverySampleTime cell hold clock clockCode channel holdInitial voltageInitial currentInitial first).value) := by
  exact cell.driven_nand_from_arbitrary_initial leftBit rightBit left right
    (loadedCapacitorEndVoltage cell hold clock clockCode channel holdInitial voltageInitial currentInitial)
    leftContinuous rightContinuous first _ firstNonnegative
    (finiteSamplingClock_requested_le_sampleTime clock clockCode _) stable

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
