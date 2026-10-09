import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor036.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile036
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample072.localBox,Sample072.localReductions,Sample072.material,Sample072.matrixRows,Sample072.densityRows⟩
  hull := ⟨Sample073.localBox,Sample073.localReductions,Sample073.material,Sample073.matrixRows,Sample073.densityRows⟩

theorem center_source : Sample072.center = HighJet.center 36 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample073.localBox = HighJet.tileBox 36 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 36 evaluation where
  center := ⟨Sample072.groupCalculations,Sample072.orbitalCalculations,Sample072.matrixCertificate,Sample072.densityComputed⟩
  hull := ⟨Sample073.groupCalculations,Sample073.orbitalCalculations,Sample073.matrixCertificate,Sample073.densityComputed⟩
  centerBox := fun a => by
    change Sample072.localBox a = _
    rw [Sample072.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 36) (callBox (HighJet.tileCall 36 i))
      Sample072.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 36 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 36 i)) x :=
  tileEvaluation_actual 36 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile036
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
