import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor055.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile055
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample110.localBox,Sample110.localReductions,Sample110.material,Sample110.matrixRows,Sample110.densityRows⟩
  hull := ⟨Sample111.localBox,Sample111.localReductions,Sample111.material,Sample111.matrixRows,Sample111.densityRows⟩

theorem center_source : Sample110.center = HighJet.center 55 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample111.localBox = HighJet.tileBox 55 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 55 evaluation where
  center := ⟨Sample110.groupCalculations,Sample110.orbitalCalculations,Sample110.matrixCertificate,Sample110.densityComputed⟩
  hull := ⟨Sample111.groupCalculations,Sample111.orbitalCalculations,Sample111.matrixCertificate,Sample111.densityComputed⟩
  centerBox := fun a => by
    change Sample110.localBox a = _
    rw [Sample110.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 55) (callBox (HighJet.tileCall 55 i))
      Sample110.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 55 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 55 i)) x :=
  tileEvaluation_actual 55 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile055
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
