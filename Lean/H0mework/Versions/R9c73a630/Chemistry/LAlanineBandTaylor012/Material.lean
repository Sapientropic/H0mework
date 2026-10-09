import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor012.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile012
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample024.localBox,Sample024.localReductions,Sample024.material,Sample024.matrixRows,Sample024.densityRows⟩
  hull := ⟨Sample025.localBox,Sample025.localReductions,Sample025.material,Sample025.matrixRows,Sample025.densityRows⟩

theorem center_source : Sample024.center = HighJet.center 12 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample025.localBox = HighJet.tileBox 12 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 12 evaluation where
  center := ⟨Sample024.groupCalculations,Sample024.orbitalCalculations,Sample024.matrixCertificate,Sample024.densityComputed⟩
  hull := ⟨Sample025.groupCalculations,Sample025.orbitalCalculations,Sample025.matrixCertificate,Sample025.densityComputed⟩
  centerBox := fun a => by
    change Sample024.localBox a = _
    rw [Sample024.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 12) (callBox (HighJet.tileCall 12 i))
      Sample024.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 12 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 12 i)) x :=
  tileEvaluation_actual 12 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile012
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
