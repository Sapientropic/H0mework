import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor035.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile035
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample070.localBox,Sample070.localReductions,Sample070.material,Sample070.matrixRows,Sample070.densityRows⟩
  hull := ⟨Sample071.localBox,Sample071.localReductions,Sample071.material,Sample071.matrixRows,Sample071.densityRows⟩

theorem center_source : Sample070.center = HighJet.center 35 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample071.localBox = HighJet.tileBox 35 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 35 evaluation where
  center := ⟨Sample070.groupCalculations,Sample070.orbitalCalculations,Sample070.matrixCertificate,Sample070.densityComputed⟩
  hull := ⟨Sample071.groupCalculations,Sample071.orbitalCalculations,Sample071.matrixCertificate,Sample071.densityComputed⟩
  centerBox := fun a => by
    change Sample070.localBox a = _
    rw [Sample070.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 35) (callBox (HighJet.tileCall 35 i))
      Sample070.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 35 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 35 i)) x :=
  tileEvaluation_actual 35 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile035
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
