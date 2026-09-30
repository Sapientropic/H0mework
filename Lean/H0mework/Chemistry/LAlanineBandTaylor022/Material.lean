import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor022.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile022
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample044.localBox,Sample044.localReductions,Sample044.material,Sample044.matrixRows,Sample044.densityRows⟩
  hull := ⟨Sample045.localBox,Sample045.localReductions,Sample045.material,Sample045.matrixRows,Sample045.densityRows⟩

theorem center_source : Sample044.center = HighJet.center 22 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample045.localBox = HighJet.tileBox 22 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 22 evaluation where
  center := ⟨Sample044.groupCalculations,Sample044.orbitalCalculations,Sample044.matrixCertificate,Sample044.densityComputed⟩
  hull := ⟨Sample045.groupCalculations,Sample045.orbitalCalculations,Sample045.matrixCertificate,Sample045.densityComputed⟩
  centerBox := fun a => by
    change Sample044.localBox a = _
    rw [Sample044.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 22) (callBox (HighJet.tileCall 22 i))
      Sample044.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 22 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 22 i)) x :=
  tileEvaluation_actual 22 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile022
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
