import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor001.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile001
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample002.localBox,Sample002.localReductions,Sample002.material,Sample002.matrixRows,Sample002.densityRows⟩
  hull := ⟨Sample003.localBox,Sample003.localReductions,Sample003.material,Sample003.matrixRows,Sample003.densityRows⟩

theorem center_source : Sample002.center = HighJet.center 1 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample003.localBox = HighJet.tileBox 1 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 1 evaluation where
  center := ⟨Sample002.groupCalculations,Sample002.orbitalCalculations,Sample002.matrixCertificate,Sample002.densityComputed⟩
  hull := ⟨Sample003.groupCalculations,Sample003.orbitalCalculations,Sample003.matrixCertificate,Sample003.densityComputed⟩
  centerBox := fun a => by
    change Sample002.localBox a = _
    rw [Sample002.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 1) (callBox (HighJet.tileCall 1 i))
      Sample002.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 1 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 1 i)) x :=
  tileEvaluation_actual 1 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile001
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
