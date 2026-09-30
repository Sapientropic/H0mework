import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor038.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile038
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample076.localBox,Sample076.localReductions,Sample076.material,Sample076.matrixRows,Sample076.densityRows⟩
  hull := ⟨Sample077.localBox,Sample077.localReductions,Sample077.material,Sample077.matrixRows,Sample077.densityRows⟩

theorem center_source : Sample076.center = HighJet.center 38 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample077.localBox = HighJet.tileBox 38 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 38 evaluation where
  center := ⟨Sample076.groupCalculations,Sample076.orbitalCalculations,Sample076.matrixCertificate,Sample076.densityComputed⟩
  hull := ⟨Sample077.groupCalculations,Sample077.orbitalCalculations,Sample077.matrixCertificate,Sample077.densityComputed⟩
  centerBox := fun a => by
    change Sample076.localBox a = _
    rw [Sample076.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 38) (callBox (HighJet.tileCall 38 i))
      Sample076.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 38 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 38 i)) x :=
  tileEvaluation_actual 38 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile038
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
