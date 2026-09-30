import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor062.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile062
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample124.localBox,Sample124.localReductions,Sample124.material,Sample124.matrixRows,Sample124.densityRows⟩
  hull := ⟨Sample125.localBox,Sample125.localReductions,Sample125.material,Sample125.matrixRows,Sample125.densityRows⟩

theorem center_source : Sample124.center = HighJet.center 62 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample125.localBox = HighJet.tileBox 62 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 62 evaluation where
  center := ⟨Sample124.groupCalculations,Sample124.orbitalCalculations,Sample124.matrixCertificate,Sample124.densityComputed⟩
  hull := ⟨Sample125.groupCalculations,Sample125.orbitalCalculations,Sample125.matrixCertificate,Sample125.densityComputed⟩
  centerBox := fun a => by
    change Sample124.localBox a = _
    rw [Sample124.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 62) (callBox (HighJet.tileCall 62 i))
      Sample124.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 62 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 62 i)) x :=
  tileEvaluation_actual 62 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile062
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
