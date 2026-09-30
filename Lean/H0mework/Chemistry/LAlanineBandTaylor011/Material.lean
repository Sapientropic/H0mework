import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor011.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile011
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample022.localBox,Sample022.localReductions,Sample022.material,Sample022.matrixRows,Sample022.densityRows⟩
  hull := ⟨Sample023.localBox,Sample023.localReductions,Sample023.material,Sample023.matrixRows,Sample023.densityRows⟩

theorem center_source : Sample022.center = HighJet.center 11 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample023.localBox = HighJet.tileBox 11 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 11 evaluation where
  center := ⟨Sample022.groupCalculations,Sample022.orbitalCalculations,Sample022.matrixCertificate,Sample022.densityComputed⟩
  hull := ⟨Sample023.groupCalculations,Sample023.orbitalCalculations,Sample023.matrixCertificate,Sample023.densityComputed⟩
  centerBox := fun a => by
    change Sample022.localBox a = _
    rw [Sample022.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 11) (callBox (HighJet.tileCall 11 i))
      Sample022.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 11 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 11 i)) x :=
  tileEvaluation_actual 11 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile011
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
