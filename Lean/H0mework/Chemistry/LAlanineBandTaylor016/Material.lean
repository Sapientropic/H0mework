import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor016.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile016
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample032.localBox,Sample032.localReductions,Sample032.material,Sample032.matrixRows,Sample032.densityRows⟩
  hull := ⟨Sample033.localBox,Sample033.localReductions,Sample033.material,Sample033.matrixRows,Sample033.densityRows⟩

theorem center_source : Sample032.center = HighJet.center 16 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample033.localBox = HighJet.tileBox 16 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 16 evaluation where
  center := ⟨Sample032.groupCalculations,Sample032.orbitalCalculations,Sample032.matrixCertificate,Sample032.densityComputed⟩
  hull := ⟨Sample033.groupCalculations,Sample033.orbitalCalculations,Sample033.matrixCertificate,Sample033.densityComputed⟩
  centerBox := fun a => by
    change Sample032.localBox a = _
    rw [Sample032.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 16) (callBox (HighJet.tileCall 16 i))
      Sample032.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 16 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 16 i)) x :=
  tileEvaluation_actual 16 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile016
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
