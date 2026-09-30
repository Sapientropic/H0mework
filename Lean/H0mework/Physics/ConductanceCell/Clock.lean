import H0mework.Physics.ConductanceCell.Dynamics
import H0mework.Physics.ConductanceCell.Bands
import H0mework.Physics.Measurement.ADC

/-!
# Continuous input bands generate restored rails and a source-clocked receipt

The same positive-leakage topology works on complete input intervals. The cell
generates its own uniform waiting time; the existing clock compiler rounds it
up. Inputs are held during this cell run. No latch or whole-graph switching
claim is inferred from that held-input model.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

def BitBand (source : LoadedConductanceCellSource) (bit : Bool) (voltage : SIVolt) : Prop :=
  if bit then HighBand source voltage else LowBand source voltage

/-- This consumer sees only the voltage, never the topology or requested truth table. -/
def railRead? (source : LoadedConductanceCellSource) (voltage : SIVolt) : Option Bool := by
  classical
  exact if LowBand source voltage then some false
    else if HighBand source voltage then some true else none

theorem railRead?_of_low (source : LoadedConductanceCellSource) (voltage : SIVolt)
    (low : LowBand source voltage) : railRead? source voltage = some false := by
  simp only [railRead?, if_pos low]

theorem railRead?_of_high (source : LoadedConductanceCellSource) (voltage : SIVolt)
    (high : HighBand source voltage) : railRead? source voltage = some true := by
  have notLow : ¬ LowBand source voltage := by
    intro low
    have supply := source.supply_pos
    linarith [low.2, high.1]
  simp only [railRead?, if_neg notLow, if_pos high]

namespace LoadedConductanceCellSource

theorem flowAt_low_of_high_high (source : LoadedConductanceCellSource)
    (left right initial : SIVolt) (leftHigh : HighBand source left)
    (rightHigh : HighBand source right) (initialRail : InRail source initial)
    (time : SISecond) (late : source.settlingTime.value ≤ time.value) :
    LowBand source (source.flowAt left right initial time) := by
  have error := (abs_lt.mp (source.voltageAt_settles left right initial initialRail time.value late)).2
  have eqBound := source.equilibrium_le_eighth_of_high_high left right leftHigh rightHigh
  have rail := source.voltageAt_mem_rail left right initial initialRail time.value
    (source.settlingTime_pos.le.trans late)
  exact ⟨rail.1, by change source.voltageAt left right initial time.value ≤ _; linarith⟩

theorem flowAt_high_of_low (source : LoadedConductanceCellSource)
    (left right initial : SIVolt) (low : LowBand source left ∨ LowBand source right)
    (initialRail : InRail source initial) (time : SISecond)
    (late : source.settlingTime.value ≤ time.value) :
    HighBand source (source.flowAt left right initial time) := by
  have error := (abs_lt.mp (source.voltageAt_settles left right initial initialRail time.value late)).1
  have eqBound : 7 * source.supply.value / 8 ≤ (source.equilibrium left right).value := by
    rcases low with leftLow | rightLow
    · exact source.seven_eighths_le_equilibrium_of_low_left left right leftLow
    · exact source.seven_eighths_le_equilibrium_of_low_right left right rightLow
  have rail := source.voltageAt_mem_rail left right initial initialRail time.value
    (source.settlingTime_pos.le.trans late)
  exact ⟨by change _ ≤ source.voltageAt left right initial time.value; linarith, rail.2⟩

theorem flowAt_nand_band (source : LoadedConductanceCellSource)
    (leftBit rightBit : Bool) (left right initial : SIVolt)
    (leftBand : BitBand source leftBit left) (rightBand : BitBand source rightBit right)
    (initialRail : InRail source initial) (time : SISecond)
    (late : source.settlingTime.value ≤ time.value) :
    BitBand source (!(leftBit && rightBit)) (source.flowAt left right initial time) := by
  cases leftBit <;> cases rightBit
  · exact source.flowAt_high_of_low left right initial (Or.inl leftBand) initialRail time late
  · exact source.flowAt_high_of_low left right initial (Or.inl leftBand) initialRail time late
  · exact source.flowAt_high_of_low left right initial (Or.inr rightBand) initialRail time late
  · exact source.flowAt_low_of_high_high left right initial leftBand rightBand initialRail time late

theorem flowAt_nand_read (source : LoadedConductanceCellSource)
    (leftBit rightBit : Bool) (left right initial : SIVolt)
    (leftBand : BitBand source leftBit left) (rightBand : BitBand source rightBit right)
    (initialRail : InRail source initial) (time : SISecond)
    (late : source.settlingTime.value ≤ time.value) :
    railRead? source (source.flowAt left right initial time) = some (!(leftBit && rightBit)) := by
  have band := source.flowAt_nand_band leftBit rightBit left right initial leftBand rightBand initialRail time late
  cases result : !(leftBit && rightBit)
  · exact railRead?_of_low source _ (by simpa only [result, BitBand, Bool.false_eq_true, ↓reduceIte] using band)
  · exact railRead?_of_high source _ (by simpa only [result, BitBand, ↓reduceIte] using band)

def sampledTime (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) : SISecond :=
  finiteSamplingClockSampleTime clockSource code source.settlingTime

def ticks (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) : Nat :=
  finiteSamplingClockTickCount clockSource code source.settlingTime

theorem sampledTime_eq_ticks (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) :
    (source.sampledTime clockSource code).value =
      (source.ticks clockSource code : ℝ) * (finiteSamplingClockTickPeriod clockSource code).value := rfl

theorem sampledTime_late (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) :
    source.settlingTime.value ≤ (source.sampledTime clockSource code).value :=
  finiteSamplingClock_requested_le_sampleTime clockSource code source.settlingTime

theorem ticks_pos (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) : 0 < source.ticks clockSource code := by
  have late := source.sampledTime_late clockSource code
  rw [source.sampledTime_eq_ticks] at late
  by_contra notPositive
  have zero : source.ticks clockSource code = 0 := by omega
  rw [zero, Nat.cast_zero, zero_mul] at late
  exact (not_le_of_gt source.settlingTime_pos) late

theorem sampled_nand (source : LoadedConductanceCellSource) (clockSource : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) (leftBit rightBit : Bool) (left right initial : SIVolt)
    (leftBand : BitBand source leftBit left) (rightBand : BitBand source rightBit right)
    (initialRail : InRail source initial) :
    BitBand source (!(leftBit && rightBit))
      (source.flowAt left right initial (source.sampledTime clockSource code)) ∧
    railRead? source (source.flowAt left right initial (source.sampledTime clockSource code)) =
      some (!(leftBit && rightBit)) :=
  ⟨source.flowAt_nand_band leftBit rightBit left right initial leftBand rightBand initialRail _
      (source.sampledTime_late clockSource code),
    source.flowAt_nand_read leftBit rightBit left right initial leftBand rightBand initialRail _
      (source.sampledTime_late clockSource code)⟩

theorem settlingTime_eq (source : LoadedConductanceCellSource) :
    source.settlingTime.value = 1152 * source.resistance.value * source.capacitance.value := by
  have supplyNonzero := ne_of_gt source.supply_pos
  unfold settlingTime positiveExponentialSettlingTime minimumRate
  dsimp only
  field_simp
  ring

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
