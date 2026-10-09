import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor041.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile041
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample082.localBox,Sample082.localReductions,Sample082.material,Sample082.matrixRows,Sample082.densityRows⟩
  hull := ⟨Sample083.localBox,Sample083.localReductions,Sample083.material,Sample083.matrixRows,Sample083.densityRows⟩

theorem center_source : Sample082.center = HighJet.center 41 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample083.localBox = HighJet.tileBox 41 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 41 evaluation where
  center := ⟨Sample082.groupCalculations,Sample082.orbitalCalculations,Sample082.matrixCertificate,Sample082.densityComputed⟩
  hull := ⟨Sample083.groupCalculations,Sample083.orbitalCalculations,Sample083.matrixCertificate,Sample083.densityComputed⟩
  centerBox := fun a => by
    change Sample082.localBox a = _
    rw [Sample082.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 41) (callBox (HighJet.tileCall 41 i))
      Sample082.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 41 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 41 i)) x :=
  tileEvaluation_actual 41 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile041
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
