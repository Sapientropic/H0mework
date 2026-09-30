import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor020.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile020
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample040.localBox,Sample040.localReductions,Sample040.material,Sample040.matrixRows,Sample040.densityRows⟩
  hull := ⟨Sample041.localBox,Sample041.localReductions,Sample041.material,Sample041.matrixRows,Sample041.densityRows⟩

theorem center_source : Sample040.center = HighJet.center 20 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample041.localBox = HighJet.tileBox 20 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 20 evaluation where
  center := ⟨Sample040.groupCalculations,Sample040.orbitalCalculations,Sample040.matrixCertificate,Sample040.densityComputed⟩
  hull := ⟨Sample041.groupCalculations,Sample041.orbitalCalculations,Sample041.matrixCertificate,Sample041.densityComputed⟩
  centerBox := fun a => by
    change Sample040.localBox a = _
    rw [Sample040.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 20) (callBox (HighJet.tileCall 20 i))
      Sample040.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 20 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 20 i)) x :=
  tileEvaluation_actual 20 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile020
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
