import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor017.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile017
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample034.localBox,Sample034.localReductions,Sample034.material,Sample034.matrixRows,Sample034.densityRows⟩
  hull := ⟨Sample035.localBox,Sample035.localReductions,Sample035.material,Sample035.matrixRows,Sample035.densityRows⟩

theorem center_source : Sample034.center = HighJet.center 17 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample035.localBox = HighJet.tileBox 17 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 17 evaluation where
  center := ⟨Sample034.groupCalculations,Sample034.orbitalCalculations,Sample034.matrixCertificate,Sample034.densityComputed⟩
  hull := ⟨Sample035.groupCalculations,Sample035.orbitalCalculations,Sample035.matrixCertificate,Sample035.densityComputed⟩
  centerBox := fun a => by
    change Sample034.localBox a = _
    rw [Sample034.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 17) (callBox (HighJet.tileCall 17 i))
      Sample034.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 17 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 17 i)) x :=
  tileEvaluation_actual 17 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile017
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
