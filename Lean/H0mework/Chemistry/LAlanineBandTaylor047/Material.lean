import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor047.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile047
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample094.localBox,Sample094.localReductions,Sample094.material,Sample094.matrixRows,Sample094.densityRows⟩
  hull := ⟨Sample095.localBox,Sample095.localReductions,Sample095.material,Sample095.matrixRows,Sample095.densityRows⟩

theorem center_source : Sample094.center = HighJet.center 47 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample095.localBox = HighJet.tileBox 47 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 47 evaluation where
  center := ⟨Sample094.groupCalculations,Sample094.orbitalCalculations,Sample094.matrixCertificate,Sample094.densityComputed⟩
  hull := ⟨Sample095.groupCalculations,Sample095.orbitalCalculations,Sample095.matrixCertificate,Sample095.densityComputed⟩
  centerBox := fun a => by
    change Sample094.localBox a = _
    rw [Sample094.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 47) (callBox (HighJet.tileCall 47 i))
      Sample094.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 47 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 47 i)) x :=
  tileEvaluation_actual 47 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile047
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
