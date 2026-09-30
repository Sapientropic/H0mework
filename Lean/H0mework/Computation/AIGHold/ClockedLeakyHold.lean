import H0mework.Physics.ConductanceCell.Clock

/-!
# Explicit switching law for a capacitor with a nonzero leakage resistance

The pre-switch waveform is retained pointwise. After the external stop event,
the same capacitor discharges from the voltage actually present at that event.
Capture margins are independent output consumers, not source fields.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Units.Interface Cells.Conductance Set

def CaptureLow (source : LoadedConductanceCellSource) (voltage : SIVolt) : Prop :=
  0 ≤ voltage.value ∧ voltage.value ≤ 7 * source.supply.value / 32

def CaptureHigh (source : LoadedConductanceCellSource) (voltage : SIVolt) : Prop :=
  27 * source.supply.value / 32 ≤ voltage.value ∧ voltage.value ≤ source.supply.value

def CaptureBand (source : LoadedConductanceCellSource) (bit : Bool) (voltage : SIVolt) : Prop :=
  if bit then CaptureHigh source voltage else CaptureLow source voltage

structure ClockedLeakyHoldSource (source : LoadedConductanceCellSource) where
  holdResistance : SIOhm
  holdResistance_pos : 0 < holdResistance.value

noncomputable section
namespace ClockedLeakyHoldSource

variable {source : LoadedConductanceCellSource}

def timeConstant (hold : ClockedLeakyHoldSource source) : SISecond :=
  ⟨hold.holdResistance.value * source.capacitance.value⟩

theorem timeConstant_pos (hold : ClockedLeakyHoldSource source) :
    0 < hold.timeConstant.value :=
  mul_pos hold.holdResistance_pos source.capacitance_pos

def retentionTime (hold : ClockedLeakyHoldSource source) : SISecond :=
  ⟨hold.timeConstant.value / 16⟩

theorem retentionTime_pos (hold : ClockedLeakyHoldSource source) :
    0 < hold.retentionTime.value := div_pos hold.timeConstant_pos (by norm_num)

def decayAt (hold : ClockedLeakyHoldSource source) (capture : SIVolt)
    (stopTime time : ℝ) : ℝ :=
  capture.value * Real.exp (-(time - stopTime) / hold.timeConstant.value)

def voltageAt (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : ℝ :=
  if time ≤ stopTime then (input time).value else hold.decayAt (input stopTime) stopTime time

def wave (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : SIVolt :=
  ⟨hold.voltageAt input stopTime time⟩

@[simp] theorem decayAt_stop (hold : ClockedLeakyHoldSource source) (capture : SIVolt)
    (stopTime : ℝ) : hold.decayAt capture stopTime stopTime = capture.value := by
  simp [decayAt]

theorem voltageAt_before (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (before : time ≤ stopTime) :
    hold.voltageAt input stopTime time = (input time).value := by
  simp only [voltageAt, if_pos before]

@[simp] theorem wave_stop (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime : ℝ) : hold.wave input stopTime stopTime = input stopTime := by
  apply SIQuantity.ext
  exact hold.voltageAt_before input stopTime stopTime le_rfl

theorem voltageAt_after (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    hold.voltageAt input stopTime time = hold.decayAt (input stopTime) stopTime time := by
  by_cases atStop : time = stopTime
  · subst time
    simp [voltageAt]
  · exact if_neg (fun before => atStop (le_antisymm before afterStop))

theorem decayAt_continuous (hold : ClockedLeakyHoldSource source) (capture : SIVolt)
    (stopTime : ℝ) : Continuous (hold.decayAt capture stopTime) := by
  unfold decayAt
  fun_prop

theorem voltageAt_continuous (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (inputContinuous : Continuous (fun t => (input t).value)) (stopTime : ℝ) :
    Continuous (hold.voltageAt input stopTime) := by
  exact inputContinuous.if_le (hold.decayAt_continuous (input stopTime) stopTime)
    continuous_id continuous_const (by intro time same; subst time; simp)

theorem decayAt_hasDerivAt (hold : ClockedLeakyHoldSource source) (capture : SIVolt)
    (stopTime time : ℝ) :
    HasDerivAt (hold.decayAt capture stopTime)
      (-hold.decayAt capture stopTime time / hold.timeConstant.value) time := by
  have derivative := (((hasDerivAt_id time).sub_const stopTime).neg.div_const
    hold.timeConstant.value).exp.const_mul capture.value
  convert derivative using 1 <;> first | rfl | (dsimp [decayAt]; ring)

/-- Right-sided KCL includes the switch endpoint without asserting two-sided differentiability. -/
theorem voltageAt_kcl (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    HasDerivWithinAt (hold.voltageAt input stopTime)
      (-hold.voltageAt input stopTime time / hold.timeConstant.value) (Ici stopTime) time := by
  rw [hold.voltageAt_after input stopTime time afterStop]
  exact (hold.decayAt_hasDerivAt (input stopTime) stopTime time).hasDerivWithinAt.congr_of_mem
    (fun t ht => hold.voltageAt_after input stopTime t ht) afterStop

theorem voltageAt_hasDerivAt (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (afterStop : stopTime < time) :
    HasDerivAt (hold.voltageAt input stopTime)
      (-hold.voltageAt input stopTime time / hold.timeConstant.value) time :=
  (hold.voltageAt_kcl input stopTime time afterStop.le).hasDerivAt (Ici_mem_nhds afterStop)

theorem capacitor_kcl (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    HasDerivWithinAt (fun t => source.capacitance.value * hold.voltageAt input stopTime t)
      (-hold.voltageAt input stopTime time / hold.holdResistance.value) (Ici stopTime) time := by
  have derivative := (hold.voltageAt_kcl input stopTime time afterStop).const_mul source.capacitance.value
  have capNonzero := ne_of_gt source.capacitance_pos
  have resistanceNonzero := ne_of_gt hold.holdResistance_pos
  convert derivative using 1 <;> first | rfl | (dsimp only [timeConstant]; field_simp)

def storedEnergyAt (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : SIJoule :=
  ⟨source.capacitance.value / 2 * hold.voltageAt input stopTime time ^ 2⟩

def dissipatedPowerAt (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : SIWatt :=
  ⟨hold.voltageAt input stopTime time ^ 2 / hold.holdResistance.value⟩

theorem dissipatedPowerAt_nonneg (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : 0 ≤ (hold.dissipatedPowerAt input stopTime time).value :=
  div_nonneg (sq_nonneg _) hold.holdResistance_pos.le

theorem storedEnergyAt_nonneg (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) : 0 ≤ (hold.storedEnergyAt input stopTime time).value :=
  mul_nonneg (div_nonneg source.capacitance_pos.le (by norm_num)) (sq_nonneg _)

/-- Stored charge and dissipated heat consume the same actual switched trajectory. -/
theorem storedEnergyAt_power_balance (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    HasDerivWithinAt (fun t => (hold.storedEnergyAt input stopTime t).value)
      (-(hold.dissipatedPowerAt input stopTime time).value) (Ici stopTime) time := by
  have derivative := ((hold.voltageAt_kcl input stopTime time afterStop).pow 2).const_mul
    (source.capacitance.value / 2)
  have capNonzero := ne_of_gt source.capacitance_pos
  have resistanceNonzero := ne_of_gt hold.holdResistance_pos
  convert derivative using 1 <;> first | rfl | (
    dsimp only [storedEnergyAt, dissipatedPowerAt, timeConstant]
    field_simp
    ring)

end ClockedLeakyHoldSource
end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
