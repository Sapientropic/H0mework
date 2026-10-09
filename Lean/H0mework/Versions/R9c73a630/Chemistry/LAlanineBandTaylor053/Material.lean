import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor053.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile053
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample106.localBox,Sample106.localReductions,Sample106.material,Sample106.matrixRows,Sample106.densityRows⟩
  hull := ⟨Sample107.localBox,Sample107.localReductions,Sample107.material,Sample107.matrixRows,Sample107.densityRows⟩

theorem center_source : Sample106.center = HighJet.center 53 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample107.localBox = HighJet.tileBox 53 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 53 evaluation where
  center := ⟨Sample106.groupCalculations,Sample106.orbitalCalculations,Sample106.matrixCertificate,Sample106.densityComputed⟩
  hull := ⟨Sample107.groupCalculations,Sample107.orbitalCalculations,Sample107.matrixCertificate,Sample107.densityComputed⟩
  centerBox := fun a => by
    change Sample106.localBox a = _
    rw [Sample106.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 53) (callBox (HighJet.tileCall 53 i))
      Sample106.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 53 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 53 i)) x :=
  tileEvaluation_actual 53 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile053
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
