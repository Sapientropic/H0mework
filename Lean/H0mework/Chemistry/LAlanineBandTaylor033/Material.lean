import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor033.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile033
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample066.localBox,Sample066.localReductions,Sample066.material,Sample066.matrixRows,Sample066.densityRows⟩
  hull := ⟨Sample067.localBox,Sample067.localReductions,Sample067.material,Sample067.matrixRows,Sample067.densityRows⟩

theorem center_source : Sample066.center = HighJet.center 33 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample067.localBox = HighJet.tileBox 33 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 33 evaluation where
  center := ⟨Sample066.groupCalculations,Sample066.orbitalCalculations,Sample066.matrixCertificate,Sample066.densityComputed⟩
  hull := ⟨Sample067.groupCalculations,Sample067.orbitalCalculations,Sample067.matrixCertificate,Sample067.densityComputed⟩
  centerBox := fun a => by
    change Sample066.localBox a = _
    rw [Sample066.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 33) (callBox (HighJet.tileCall 33 i))
      Sample066.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 33 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 33 i)) x :=
  tileEvaluation_actual 33 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile033
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
