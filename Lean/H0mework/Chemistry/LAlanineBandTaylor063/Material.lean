import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor063.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile063
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample126.localBox,Sample126.localReductions,Sample126.material,Sample126.matrixRows,Sample126.densityRows⟩
  hull := ⟨Sample127.localBox,Sample127.localReductions,Sample127.material,Sample127.matrixRows,Sample127.densityRows⟩

theorem center_source : Sample126.center = HighJet.center 63 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample127.localBox = HighJet.tileBox 63 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 63 evaluation where
  center := ⟨Sample126.groupCalculations,Sample126.orbitalCalculations,Sample126.matrixCertificate,Sample126.densityComputed⟩
  hull := ⟨Sample127.groupCalculations,Sample127.orbitalCalculations,Sample127.matrixCertificate,Sample127.densityComputed⟩
  centerBox := fun a => by
    change Sample126.localBox a = _
    rw [Sample126.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 63) (callBox (HighJet.tileCall 63 i))
      Sample126.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 63 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 63 i)) x :=
  tileEvaluation_actual 63 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile063
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
