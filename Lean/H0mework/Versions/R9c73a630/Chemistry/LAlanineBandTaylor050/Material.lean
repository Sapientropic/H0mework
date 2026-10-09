import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor050.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile050
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample100.localBox,Sample100.localReductions,Sample100.material,Sample100.matrixRows,Sample100.densityRows⟩
  hull := ⟨Sample101.localBox,Sample101.localReductions,Sample101.material,Sample101.matrixRows,Sample101.densityRows⟩

theorem center_source : Sample100.center = HighJet.center 50 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample101.localBox = HighJet.tileBox 50 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 50 evaluation where
  center := ⟨Sample100.groupCalculations,Sample100.orbitalCalculations,Sample100.matrixCertificate,Sample100.densityComputed⟩
  hull := ⟨Sample101.groupCalculations,Sample101.orbitalCalculations,Sample101.matrixCertificate,Sample101.densityComputed⟩
  centerBox := fun a => by
    change Sample100.localBox a = _
    rw [Sample100.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 50) (callBox (HighJet.tileCall 50 i))
      Sample100.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 50 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 50 i)) x :=
  tileEvaluation_actual 50 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile050
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
