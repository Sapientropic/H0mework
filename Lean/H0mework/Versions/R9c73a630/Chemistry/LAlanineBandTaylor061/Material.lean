import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor061.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile061
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample122.localBox,Sample122.localReductions,Sample122.material,Sample122.matrixRows,Sample122.densityRows⟩
  hull := ⟨Sample123.localBox,Sample123.localReductions,Sample123.material,Sample123.matrixRows,Sample123.densityRows⟩

theorem center_source : Sample122.center = HighJet.center 61 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample123.localBox = HighJet.tileBox 61 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 61 evaluation where
  center := ⟨Sample122.groupCalculations,Sample122.orbitalCalculations,Sample122.matrixCertificate,Sample122.densityComputed⟩
  hull := ⟨Sample123.groupCalculations,Sample123.orbitalCalculations,Sample123.matrixCertificate,Sample123.densityComputed⟩
  centerBox := fun a => by
    change Sample122.localBox a = _
    rw [Sample122.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 61) (callBox (HighJet.tileCall 61 i))
      Sample122.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 61 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 61 i)) x :=
  tileEvaluation_actual 61 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile061
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
