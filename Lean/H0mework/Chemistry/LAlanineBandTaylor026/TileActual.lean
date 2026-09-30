import H0mework.Chemistry.LAlanineBandTaylor026.TileReports
import H0mework.Chemistry.LAlanineBandTaylor026.HullBounds

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile026
open SourceGaussianModel SourceSignedEvaluator WholeBandSource

theorem center_interval (a : Fin 3) :
    (Sample053.localBox a).1 ≤ Sample052.center a ∧ Sample052.center a ≤ (Sample053.localBox a).2 := by
  fin_cases a <;> decide +kernel

theorem source_restriction (i : HighJet.Slot) (a : Fin 3) :
    HighJet.PairWithin (callBox (HighJet.tileCall 26 i) a) (Sample053.localBox a) := by
  fin_cases i <;> fin_cases a <;> decide +kernel

theorem center_inside_hull : InRectangle Sample053.localBox (Taylor.centerPoint Sample052.center) := by
  intro a
  exact ⟨Rat.cast_le.mpr (center_interval a).1,Rat.cast_le.mpr (center_interval a).2⟩

theorem call_inside_hull (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 26 i)) x) : InRectangle Sample053.localBox x :=
  fun a => HighJet.pairWithin_holds (source_restriction i a) (x a) (inside a)

theorem actual_field (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 26 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 26 i)) x :=
  HighJet.fieldWithin_holds (all_reports i) x
    (Taylor.fieldEnclosure_contains Sample052.center (callBox (HighJet.tileCall 26 i))
      Sample053.localBox Sample052.bounds fourthBounds Sample052.center_bounds
      Sample053.fourth_bounds center_inside_hull (call_inside_hull i) x inside)
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile026
