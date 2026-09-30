import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor006.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile006
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample012.localBox,Sample012.localReductions,Sample012.material,Sample012.matrixRows,Sample012.densityRows⟩
  hull := ⟨Sample013.localBox,Sample013.localReductions,Sample013.material,Sample013.matrixRows,Sample013.densityRows⟩

theorem center_source : Sample012.center = HighJet.center 6 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample013.localBox = HighJet.tileBox 6 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 6 evaluation where
  center := ⟨Sample012.groupCalculations,Sample012.orbitalCalculations,Sample012.matrixCertificate,Sample012.densityComputed⟩
  hull := ⟨Sample013.groupCalculations,Sample013.orbitalCalculations,Sample013.matrixCertificate,Sample013.densityComputed⟩
  centerBox := fun a => by
    change Sample012.localBox a = _
    rw [Sample012.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 6) (callBox (HighJet.tileCall 6 i))
      Sample012.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 6 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 6 i)) x :=
  tileEvaluation_actual 6 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile006
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
