import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor013.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile013
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample026.localBox,Sample026.localReductions,Sample026.material,Sample026.matrixRows,Sample026.densityRows⟩
  hull := ⟨Sample027.localBox,Sample027.localReductions,Sample027.material,Sample027.matrixRows,Sample027.densityRows⟩

theorem center_source : Sample026.center = HighJet.center 13 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample027.localBox = HighJet.tileBox 13 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 13 evaluation where
  center := ⟨Sample026.groupCalculations,Sample026.orbitalCalculations,Sample026.matrixCertificate,Sample026.densityComputed⟩
  hull := ⟨Sample027.groupCalculations,Sample027.orbitalCalculations,Sample027.matrixCertificate,Sample027.densityComputed⟩
  centerBox := fun a => by
    change Sample026.localBox a = _
    rw [Sample026.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 13) (callBox (HighJet.tileCall 13 i))
      Sample026.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 13 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 13 i)) x :=
  tileEvaluation_actual 13 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile013
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
