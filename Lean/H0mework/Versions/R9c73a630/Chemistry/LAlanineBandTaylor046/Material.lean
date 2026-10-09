import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor046.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile046
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample092.localBox,Sample092.localReductions,Sample092.material,Sample092.matrixRows,Sample092.densityRows⟩
  hull := ⟨Sample093.localBox,Sample093.localReductions,Sample093.material,Sample093.matrixRows,Sample093.densityRows⟩

theorem center_source : Sample092.center = HighJet.center 46 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample093.localBox = HighJet.tileBox 46 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 46 evaluation where
  center := ⟨Sample092.groupCalculations,Sample092.orbitalCalculations,Sample092.matrixCertificate,Sample092.densityComputed⟩
  hull := ⟨Sample093.groupCalculations,Sample093.orbitalCalculations,Sample093.matrixCertificate,Sample093.densityComputed⟩
  centerBox := fun a => by
    change Sample092.localBox a = _
    rw [Sample092.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 46) (callBox (HighJet.tileCall 46 i))
      Sample092.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 46 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 46 i)) x :=
  tileEvaluation_actual 46 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile046
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
