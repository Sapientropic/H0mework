import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor014.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile014
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample028.localBox,Sample028.localReductions,Sample028.material,Sample028.matrixRows,Sample028.densityRows⟩
  hull := ⟨Sample029.localBox,Sample029.localReductions,Sample029.material,Sample029.matrixRows,Sample029.densityRows⟩

theorem center_source : Sample028.center = HighJet.center 14 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample029.localBox = HighJet.tileBox 14 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 14 evaluation where
  center := ⟨Sample028.groupCalculations,Sample028.orbitalCalculations,Sample028.matrixCertificate,Sample028.densityComputed⟩
  hull := ⟨Sample029.groupCalculations,Sample029.orbitalCalculations,Sample029.matrixCertificate,Sample029.densityComputed⟩
  centerBox := fun a => by
    change Sample028.localBox a = _
    rw [Sample028.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 14) (callBox (HighJet.tileCall 14 i))
      Sample028.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 14 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 14 i)) x :=
  tileEvaluation_actual 14 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile014
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
