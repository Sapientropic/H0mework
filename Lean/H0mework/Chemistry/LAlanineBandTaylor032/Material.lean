import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor032.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile032
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample064.localBox,Sample064.localReductions,Sample064.material,Sample064.matrixRows,Sample064.densityRows⟩
  hull := ⟨Sample065.localBox,Sample065.localReductions,Sample065.material,Sample065.matrixRows,Sample065.densityRows⟩

theorem center_source : Sample064.center = HighJet.center 32 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample065.localBox = HighJet.tileBox 32 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 32 evaluation where
  center := ⟨Sample064.groupCalculations,Sample064.orbitalCalculations,Sample064.matrixCertificate,Sample064.densityComputed⟩
  hull := ⟨Sample065.groupCalculations,Sample065.orbitalCalculations,Sample065.matrixCertificate,Sample065.densityComputed⟩
  centerBox := fun a => by
    change Sample064.localBox a = _
    rw [Sample064.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 32) (callBox (HighJet.tileCall 32 i))
      Sample064.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 32 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 32 i)) x :=
  tileEvaluation_actual 32 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile032
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
