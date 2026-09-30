import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor024.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile024
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample048.localBox,Sample048.localReductions,Sample048.material,Sample048.matrixRows,Sample048.densityRows⟩
  hull := ⟨Sample049.localBox,Sample049.localReductions,Sample049.material,Sample049.matrixRows,Sample049.densityRows⟩

theorem center_source : Sample048.center = HighJet.center 24 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample049.localBox = HighJet.tileBox 24 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 24 evaluation where
  center := ⟨Sample048.groupCalculations,Sample048.orbitalCalculations,Sample048.matrixCertificate,Sample048.densityComputed⟩
  hull := ⟨Sample049.groupCalculations,Sample049.orbitalCalculations,Sample049.matrixCertificate,Sample049.densityComputed⟩
  centerBox := fun a => by
    change Sample048.localBox a = _
    rw [Sample048.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 24) (callBox (HighJet.tileCall 24 i))
      Sample048.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 24 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 24 i)) x :=
  tileEvaluation_actual 24 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile024
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
