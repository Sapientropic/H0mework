import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor054.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile054
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample108.localBox,Sample108.localReductions,Sample108.material,Sample108.matrixRows,Sample108.densityRows⟩
  hull := ⟨Sample109.localBox,Sample109.localReductions,Sample109.material,Sample109.matrixRows,Sample109.densityRows⟩

theorem center_source : Sample108.center = HighJet.center 54 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample109.localBox = HighJet.tileBox 54 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 54 evaluation where
  center := ⟨Sample108.groupCalculations,Sample108.orbitalCalculations,Sample108.matrixCertificate,Sample108.densityComputed⟩
  hull := ⟨Sample109.groupCalculations,Sample109.orbitalCalculations,Sample109.matrixCertificate,Sample109.densityComputed⟩
  centerBox := fun a => by
    change Sample108.localBox a = _
    rw [Sample108.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 54) (callBox (HighJet.tileCall 54 i))
      Sample108.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 54 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 54 i)) x :=
  tileEvaluation_actual 54 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile054
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
