import H0mework.Physics.Measurement.Units
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Loaded quartic voltage-controlled conductance source

The source contains only positive physical supply, resistance and load
capacitance. Each branch conductance reads its own gate voltage through one
fixed quartic law with leakage 1/256. Two parallel pull-up branches and two
series pull-down branches determine the equilibrium and decay rate.
This is a specified conductance model, not a MOS material instance.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface

noncomputable section

structure LoadedConductanceCellSource where
  supply : SIVolt
  resistance : SIOhm
  capacitance : SIFarad
  supply_pos : 0 < supply.value
  resistance_pos : 0 < resistance.value
  capacitance_pos : 0 < capacitance.value

/-- Single-input local constitutive law; no desired logical response is supplied. -/
def quarticNFactor (gate : ℝ) : ℝ := gate ^ 4 + 1 / 256

def quarticPFactor (gate : ℝ) : ℝ := (1 - gate) ^ 4 + 1 / 256

def parallelPFactor (left right : ℝ) : ℝ := quarticPFactor left + quarticPFactor right

def seriesNFactor (left right : ℝ) : ℝ :=
  quarticNFactor left * quarticNFactor right / (quarticNFactor left + quarticNFactor right)

theorem quarticNFactor_pos (gate : ℝ) : 0 < quarticNFactor gate := by
  unfold quarticNFactor
  positivity

theorem quarticPFactor_pos (gate : ℝ) : 0 < quarticPFactor gate :=
  quarticNFactor_pos (1 - gate)

theorem parallelPFactor_pos (left right : ℝ) : 0 < parallelPFactor left right :=
  add_pos (quarticPFactor_pos left) (quarticPFactor_pos right)

theorem seriesNFactor_pos (left right : ℝ) : 0 < seriesNFactor left right :=
  div_pos (mul_pos (quarticNFactor_pos left) (quarticNFactor_pos right))
    (add_pos (quarticNFactor_pos left) (quarticNFactor_pos right))

/-- Independent voltage consumers, defined before the cell equilibrium. -/
def InRail (source : LoadedConductanceCellSource) (voltage : SIVolt) : Prop :=
  0 ≤ voltage.value ∧ voltage.value ≤ source.supply.value

def LowBand (source : LoadedConductanceCellSource) (voltage : SIVolt) : Prop :=
  0 ≤ voltage.value ∧ voltage.value ≤ source.supply.value / 4

def HighBand (source : LoadedConductanceCellSource) (voltage : SIVolt) : Prop :=
  3 * source.supply.value / 4 ≤ voltage.value ∧ voltage.value ≤ source.supply.value

namespace LoadedConductanceCellSource

def normalizedGate (source : LoadedConductanceCellSource) (voltage : SIVolt) : ℝ :=
  voltage.value / source.supply.value

def nConductance (source : LoadedConductanceCellSource) (ownGate : SIVolt) : ℝ :=
  source.resistance.value⁻¹ * quarticNFactor (source.normalizedGate ownGate)

def pConductance (source : LoadedConductanceCellSource) (ownGate : SIVolt) : ℝ :=
  source.resistance.value⁻¹ * quarticPFactor (source.normalizedGate ownGate)

def pullUp (source : LoadedConductanceCellSource) (left right : SIVolt) : ℝ :=
  source.pConductance left + source.pConductance right

def pullDown (source : LoadedConductanceCellSource) (left right : SIVolt) : ℝ :=
  source.nConductance left * source.nConductance right /
    (source.nConductance left + source.nConductance right)

def equilibrium (source : LoadedConductanceCellSource) (left right : SIVolt) : SIVolt :=
  ⟨source.pullUp left right * source.supply.value /
    (source.pullUp left right + source.pullDown left right)⟩

def rate (source : LoadedConductanceCellSource) (left right : SIVolt) : ℝ :=
  (source.pullUp left right + source.pullDown left right) / source.capacitance.value

theorem nConductance_pos (source : LoadedConductanceCellSource) (gate : SIVolt) :
    0 < source.nConductance gate :=
  mul_pos (inv_pos.mpr source.resistance_pos) (quarticNFactor_pos _)

theorem pConductance_pos (source : LoadedConductanceCellSource) (gate : SIVolt) :
    0 < source.pConductance gate :=
  mul_pos (inv_pos.mpr source.resistance_pos) (quarticPFactor_pos _)

theorem pullUp_pos (source : LoadedConductanceCellSource) (left right : SIVolt) :
    0 < source.pullUp left right :=
  add_pos (source.pConductance_pos left) (source.pConductance_pos right)

theorem pullDown_pos (source : LoadedConductanceCellSource) (left right : SIVolt) :
    0 < source.pullDown left right :=
  div_pos (mul_pos (source.nConductance_pos left) (source.nConductance_pos right))
    (add_pos (source.nConductance_pos left) (source.nConductance_pos right))

theorem rate_pos (source : LoadedConductanceCellSource) (left right : SIVolt) :
    0 < source.rate left right :=
  div_pos (add_pos (source.pullUp_pos left right) (source.pullDown_pos left right))
    source.capacitance_pos

theorem pullUp_normalized (source : LoadedConductanceCellSource) (left right : SIVolt) :
    source.pullUp left right = source.resistance.value⁻¹ *
      parallelPFactor (source.normalizedGate left) (source.normalizedGate right) := by
  unfold pullUp pConductance parallelPFactor
  ring

theorem pullDown_normalized (source : LoadedConductanceCellSource) (left right : SIVolt) :
    source.pullDown left right = source.resistance.value⁻¹ *
      seriesNFactor (source.normalizedGate left) (source.normalizedGate right) := by
  have nonzero := ne_of_gt source.resistance_pos
  have sumNonzero := ne_of_gt (add_pos
    (quarticNFactor_pos (source.normalizedGate left))
    (quarticNFactor_pos (source.normalizedGate right)))
  unfold pullDown nConductance seriesNFactor
  field_simp

theorem equilibrium_normalized (source : LoadedConductanceCellSource) (left right : SIVolt) :
    (source.equilibrium left right).value =
      source.supply.value *
        (parallelPFactor (source.normalizedGate left) (source.normalizedGate right) /
          (parallelPFactor (source.normalizedGate left) (source.normalizedGate right) +
            seriesNFactor (source.normalizedGate left) (source.normalizedGate right))) := by
  have nonzero := ne_of_gt source.resistance_pos
  have sumNonzero := ne_of_gt (add_pos
    (parallelPFactor_pos (source.normalizedGate left) (source.normalizedGate right))
    (seriesNFactor_pos (source.normalizedGate left) (source.normalizedGate right)))
  change source.pullUp left right * source.supply.value /
    (source.pullUp left right + source.pullDown left right) = _
  rw [source.pullUp_normalized, source.pullDown_normalized]
  field_simp

theorem equilibrium_mem_rail (source : LoadedConductanceCellSource) (left right : SIVolt) :
    InRail source (source.equilibrium left right) := by
  have up := source.pullUp_pos left right
  have down := source.pullDown_pos left right
  constructor
  · exact (div_pos (mul_pos up source.supply_pos) (add_pos up down)).le
  · change source.pullUp left right * source.supply.value /
      (source.pullUp left right + source.pullDown left right) ≤ source.supply.value
    apply (div_le_iff₀ (add_pos up down)).mpr
    have comparison := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (a := source.pullUp left right) down.le)
      source.supply_pos.le
    simpa only [mul_comm] using comparison

end LoadedConductanceCellSource

end

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
