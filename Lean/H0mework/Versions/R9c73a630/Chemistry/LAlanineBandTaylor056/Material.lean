import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor056.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile056
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample112.localBox,Sample112.localReductions,Sample112.material,Sample112.matrixRows,Sample112.densityRows⟩
  hull := ⟨Sample113.localBox,Sample113.localReductions,Sample113.material,Sample113.matrixRows,Sample113.densityRows⟩

theorem center_source : Sample112.center = HighJet.center 56 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample113.localBox = HighJet.tileBox 56 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 56 evaluation where
  center := ⟨Sample112.groupCalculations,Sample112.orbitalCalculations,Sample112.matrixCertificate,Sample112.densityComputed⟩
  hull := ⟨Sample113.groupCalculations,Sample113.orbitalCalculations,Sample113.matrixCertificate,Sample113.densityComputed⟩
  centerBox := fun a => by
    change Sample112.localBox a = _
    rw [Sample112.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 56) (callBox (HighJet.tileCall 56 i))
      Sample112.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 56 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 56 i)) x :=
  tileEvaluation_actual 56 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile056
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
