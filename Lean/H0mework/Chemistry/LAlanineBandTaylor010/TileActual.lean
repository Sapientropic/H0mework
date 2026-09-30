import H0mework.Chemistry.LAlanineBandTaylor010.TileReports
import H0mework.Chemistry.LAlanineBandTaylor010.HullBounds

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile010
open SourceGaussianModel SourceSignedEvaluator WholeBandSource

theorem center_interval (a : Fin 3) :
    (Sample021.localBox a).1 ≤ Sample020.center a ∧ Sample020.center a ≤ (Sample021.localBox a).2 := by
  fin_cases a <;> decide +kernel

theorem source_restriction (i : HighJet.Slot) (a : Fin 3) :
    HighJet.PairWithin (callBox (HighJet.tileCall 10 i) a) (Sample021.localBox a) := by
  fin_cases i <;> fin_cases a <;> decide +kernel

theorem center_inside_hull : InRectangle Sample021.localBox (Taylor.centerPoint Sample020.center) := by
  intro a
  exact ⟨Rat.cast_le.mpr (center_interval a).1,Rat.cast_le.mpr (center_interval a).2⟩

theorem call_inside_hull (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 10 i)) x) : InRectangle Sample021.localBox x :=
  fun a => HighJet.pairWithin_holds (source_restriction i a) (x a) (inside a)

theorem actual_field (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 10 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 10 i)) x :=
  HighJet.fieldWithin_holds (all_reports i) x
    (Taylor.fieldEnclosure_contains Sample020.center (callBox (HighJet.tileCall 10 i))
      Sample021.localBox Sample020.bounds fourthBounds Sample020.center_bounds
      Sample021.fourth_bounds center_inside_hull (call_inside_hull i) x inside)
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile010
