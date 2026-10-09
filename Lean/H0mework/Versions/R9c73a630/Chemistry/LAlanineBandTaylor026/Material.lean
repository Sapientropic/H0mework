import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor026.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile026
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample052.localBox,Sample052.localReductions,Sample052.material,Sample052.matrixRows,Sample052.densityRows⟩
  hull := ⟨Sample053.localBox,Sample053.localReductions,Sample053.material,Sample053.matrixRows,Sample053.densityRows⟩

theorem center_source : Sample052.center = HighJet.center 26 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample053.localBox = HighJet.tileBox 26 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 26 evaluation where
  center := ⟨Sample052.groupCalculations,Sample052.orbitalCalculations,Sample052.matrixCertificate,Sample052.densityComputed⟩
  hull := ⟨Sample053.groupCalculations,Sample053.orbitalCalculations,Sample053.matrixCertificate,Sample053.densityComputed⟩
  centerBox := fun a => by
    change Sample052.localBox a = _
    rw [Sample052.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 26) (callBox (HighJet.tileCall 26 i))
      Sample052.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 26 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 26 i)) x :=
  tileEvaluation_actual 26 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile026
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
