import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor030.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile030
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample060.localBox,Sample060.localReductions,Sample060.material,Sample060.matrixRows,Sample060.densityRows⟩
  hull := ⟨Sample061.localBox,Sample061.localReductions,Sample061.material,Sample061.matrixRows,Sample061.densityRows⟩

theorem center_source : Sample060.center = HighJet.center 30 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample061.localBox = HighJet.tileBox 30 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 30 evaluation where
  center := ⟨Sample060.groupCalculations,Sample060.orbitalCalculations,Sample060.matrixCertificate,Sample060.densityComputed⟩
  hull := ⟨Sample061.groupCalculations,Sample061.orbitalCalculations,Sample061.matrixCertificate,Sample061.densityComputed⟩
  centerBox := fun a => by
    change Sample060.localBox a = _
    rw [Sample060.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 30) (callBox (HighJet.tileCall 30 i))
      Sample060.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 30 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 30 i)) x :=
  tileEvaluation_actual 30 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile030
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
