import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor023.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile023
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample046.localBox,Sample046.localReductions,Sample046.material,Sample046.matrixRows,Sample046.densityRows⟩
  hull := ⟨Sample047.localBox,Sample047.localReductions,Sample047.material,Sample047.matrixRows,Sample047.densityRows⟩

theorem center_source : Sample046.center = HighJet.center 23 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample047.localBox = HighJet.tileBox 23 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 23 evaluation where
  center := ⟨Sample046.groupCalculations,Sample046.orbitalCalculations,Sample046.matrixCertificate,Sample046.densityComputed⟩
  hull := ⟨Sample047.groupCalculations,Sample047.orbitalCalculations,Sample047.matrixCertificate,Sample047.densityComputed⟩
  centerBox := fun a => by
    change Sample046.localBox a = _
    rw [Sample046.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 23) (callBox (HighJet.tileCall 23 i))
      Sample046.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 23 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 23 i)) x :=
  tileEvaluation_actual 23 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile023
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
