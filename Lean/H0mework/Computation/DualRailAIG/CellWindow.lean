import H0mework.Physics.ConductanceCell.Restoration

/-! # Finite-window consumers of actual cell voltages -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface Set

/-- Only the admitted window is stable; earlier and later voltages are unrestricted. -/
structure CellRailWindow (source : LoadedConductanceCellSource) (bit : Bool)
    (wave : ℝ → SIVolt) (ready last : ℝ) : Prop where
  ready_nonneg : 0 ≤ ready
  continuous : Continuous (fun t => (wave t).value)
  settled : ∀ t ∈ Icc ready last, BitBand source bit (wave t)

namespace CellRailWindow

theorem constant (source : LoadedConductanceCellSource) (bit : Bool)
    (first last : ℝ) (firstNonnegative : 0 ≤ first) :
    CellRailWindow source bit (fun _ => if bit then source.supply else ⟨0⟩) first last where
  ready_nonneg := firstNonnegative
  continuous := continuous_const
  settled := by
    intro _ _
    cases bit <;> simp only [BitBand, Bool.false_eq_true, ↓reduceIte, LowBand, HighBand]
    · exact ⟨le_refl _, (div_pos source.supply_pos (by norm_num)).le⟩
    · exact ⟨by linarith [source.supply_pos], le_refl _⟩

theorem same_supply {source other : LoadedConductanceCellSource} {bit : Bool}
    {wave : ℝ → SIVolt} {ready last : ℝ}
    (actual : CellRailWindow source bit wave ready last) (same : source.supply = other.supply) :
    CellRailWindow other bit wave ready last where
  ready_nonneg := actual.ready_nonneg
  continuous := actual.continuous
  settled := by
    intro t ht
    simpa only [BitBand, LowBand, HighBand, same] using actual.settled t ht

theorem nand {source : LoadedConductanceCellSource} {leftBit rightBit : Bool}
    {left right : ℝ → SIVolt} {leftReady rightReady last : ℝ}
    (leftActual : CellRailWindow source leftBit left leftReady last)
    (rightActual : CellRailWindow source rightBit right rightReady last)
    (initial : SIVolt) (initialRail : InRail source initial) :
    CellRailWindow source (!(leftBit && rightBit))
      (fun t => ⟨source.drivenVoltageAt left right initial t⟩)
      (max leftReady rightReady + source.settlingTime.value) last where
  ready_nonneg := add_nonneg (leftActual.ready_nonneg.trans (le_max_left _ _)) source.settlingTime_pos.le
  continuous := source.drivenVoltageAt_continuous _ _ _ leftActual.continuous rightActual.continuous
  settled := by
    intro t ht
    exact source.driven_nand_band _ _ _ _ _ leftActual.continuous rightActual.continuous initialRail
      (max leftReady rightReady) t (leftActual.ready_nonneg.trans (le_max_left _ _)) ht.1
      (fun time htime =>
        ⟨leftActual.settled time ⟨(le_max_left _ _).trans htime.1, htime.2.trans ht.2⟩,
         rightActual.settled time ⟨(le_max_right _ _).trans htime.1, htime.2.trans ht.2⟩⟩)

end CellRailWindow
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
