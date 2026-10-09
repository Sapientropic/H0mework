import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor007.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile007
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample014.localBox,Sample014.localReductions,Sample014.material,Sample014.matrixRows,Sample014.densityRows⟩
  hull := ⟨Sample015.localBox,Sample015.localReductions,Sample015.material,Sample015.matrixRows,Sample015.densityRows⟩

theorem center_source : Sample014.center = HighJet.center 7 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample015.localBox = HighJet.tileBox 7 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 7 evaluation where
  center := ⟨Sample014.groupCalculations,Sample014.orbitalCalculations,Sample014.matrixCertificate,Sample014.densityComputed⟩
  hull := ⟨Sample015.groupCalculations,Sample015.orbitalCalculations,Sample015.matrixCertificate,Sample015.densityComputed⟩
  centerBox := fun a => by
    change Sample014.localBox a = _
    rw [Sample014.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 7) (callBox (HighJet.tileCall 7 i))
      Sample014.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 7 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 7 i)) x :=
  tileEvaluation_actual 7 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile007
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
