import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor004.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile004
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample008.localBox,Sample008.localReductions,Sample008.material,Sample008.matrixRows,Sample008.densityRows⟩
  hull := ⟨Sample009.localBox,Sample009.localReductions,Sample009.material,Sample009.matrixRows,Sample009.densityRows⟩

theorem center_source : Sample008.center = HighJet.center 4 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample009.localBox = HighJet.tileBox 4 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 4 evaluation where
  center := ⟨Sample008.groupCalculations,Sample008.orbitalCalculations,Sample008.matrixCertificate,Sample008.densityComputed⟩
  hull := ⟨Sample009.groupCalculations,Sample009.orbitalCalculations,Sample009.matrixCertificate,Sample009.densityComputed⟩
  centerBox := fun a => by
    change Sample008.localBox a = _
    rw [Sample008.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 4) (callBox (HighJet.tileCall 4 i))
      Sample008.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 4 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 4 i)) x :=
  tileEvaluation_actual 4 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile004
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
