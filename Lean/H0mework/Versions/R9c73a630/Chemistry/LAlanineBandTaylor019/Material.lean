import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor019.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile019
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample038.localBox,Sample038.localReductions,Sample038.material,Sample038.matrixRows,Sample038.densityRows⟩
  hull := ⟨Sample039.localBox,Sample039.localReductions,Sample039.material,Sample039.matrixRows,Sample039.densityRows⟩

theorem center_source : Sample038.center = HighJet.center 19 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample039.localBox = HighJet.tileBox 19 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 19 evaluation where
  center := ⟨Sample038.groupCalculations,Sample038.orbitalCalculations,Sample038.matrixCertificate,Sample038.densityComputed⟩
  hull := ⟨Sample039.groupCalculations,Sample039.orbitalCalculations,Sample039.matrixCertificate,Sample039.densityComputed⟩
  centerBox := fun a => by
    change Sample038.localBox a = _
    rw [Sample038.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 19) (callBox (HighJet.tileCall 19 i))
      Sample038.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 19 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 19 i)) x :=
  tileEvaluation_actual 19 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile019
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
