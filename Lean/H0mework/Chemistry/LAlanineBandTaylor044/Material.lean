import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor044.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile044
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample088.localBox,Sample088.localReductions,Sample088.material,Sample088.matrixRows,Sample088.densityRows⟩
  hull := ⟨Sample089.localBox,Sample089.localReductions,Sample089.material,Sample089.matrixRows,Sample089.densityRows⟩

theorem center_source : Sample088.center = HighJet.center 44 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample089.localBox = HighJet.tileBox 44 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 44 evaluation where
  center := ⟨Sample088.groupCalculations,Sample088.orbitalCalculations,Sample088.matrixCertificate,Sample088.densityComputed⟩
  hull := ⟨Sample089.groupCalculations,Sample089.orbitalCalculations,Sample089.matrixCertificate,Sample089.densityComputed⟩
  centerBox := fun a => by
    change Sample088.localBox a = _
    rw [Sample088.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 44) (callBox (HighJet.tileCall 44 i))
      Sample088.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 44 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 44 i)) x :=
  tileEvaluation_actual 44 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile044
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
