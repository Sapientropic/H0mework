import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor034.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile034
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample068.localBox,Sample068.localReductions,Sample068.material,Sample068.matrixRows,Sample068.densityRows⟩
  hull := ⟨Sample069.localBox,Sample069.localReductions,Sample069.material,Sample069.matrixRows,Sample069.densityRows⟩

theorem center_source : Sample068.center = HighJet.center 34 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample069.localBox = HighJet.tileBox 34 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 34 evaluation where
  center := ⟨Sample068.groupCalculations,Sample068.orbitalCalculations,Sample068.matrixCertificate,Sample068.densityComputed⟩
  hull := ⟨Sample069.groupCalculations,Sample069.orbitalCalculations,Sample069.matrixCertificate,Sample069.densityComputed⟩
  centerBox := fun a => by
    change Sample068.localBox a = _
    rw [Sample068.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 34) (callBox (HighJet.tileCall 34 i))
      Sample068.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 34 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 34 i)) x :=
  tileEvaluation_actual 34 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile034
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
