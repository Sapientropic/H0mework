import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor057.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile057
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample114.localBox,Sample114.localReductions,Sample114.material,Sample114.matrixRows,Sample114.densityRows⟩
  hull := ⟨Sample115.localBox,Sample115.localReductions,Sample115.material,Sample115.matrixRows,Sample115.densityRows⟩

theorem center_source : Sample114.center = HighJet.center 57 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample115.localBox = HighJet.tileBox 57 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 57 evaluation where
  center := ⟨Sample114.groupCalculations,Sample114.orbitalCalculations,Sample114.matrixCertificate,Sample114.densityComputed⟩
  hull := ⟨Sample115.groupCalculations,Sample115.orbitalCalculations,Sample115.matrixCertificate,Sample115.densityComputed⟩
  centerBox := fun a => by
    change Sample114.localBox a = _
    rw [Sample114.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 57) (callBox (HighJet.tileCall 57 i))
      Sample114.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 57 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 57 i)) x :=
  tileEvaluation_actual 57 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile057
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
