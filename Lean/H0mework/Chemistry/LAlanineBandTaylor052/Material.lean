import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor052.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile052
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample104.localBox,Sample104.localReductions,Sample104.material,Sample104.matrixRows,Sample104.densityRows⟩
  hull := ⟨Sample105.localBox,Sample105.localReductions,Sample105.material,Sample105.matrixRows,Sample105.densityRows⟩

theorem center_source : Sample104.center = HighJet.center 52 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample105.localBox = HighJet.tileBox 52 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 52 evaluation where
  center := ⟨Sample104.groupCalculations,Sample104.orbitalCalculations,Sample104.matrixCertificate,Sample104.densityComputed⟩
  hull := ⟨Sample105.groupCalculations,Sample105.orbitalCalculations,Sample105.matrixCertificate,Sample105.densityComputed⟩
  centerBox := fun a => by
    change Sample104.localBox a = _
    rw [Sample104.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 52) (callBox (HighJet.tileCall 52 i))
      Sample104.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 52 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 52 i)) x :=
  tileEvaluation_actual 52 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile052
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
