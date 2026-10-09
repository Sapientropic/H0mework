import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor000.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile000
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample000.localBox,Sample000.localReductions,Sample000.material,Sample000.matrixRows,Sample000.densityRows⟩
  hull := ⟨Sample001.localBox,Sample001.localReductions,Sample001.material,Sample001.matrixRows,Sample001.densityRows⟩

theorem center_source : Sample000.center = HighJet.center 0 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample001.localBox = HighJet.tileBox 0 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 0 evaluation where
  center := ⟨Sample000.groupCalculations,Sample000.orbitalCalculations,Sample000.matrixCertificate,Sample000.densityComputed⟩
  hull := ⟨Sample001.groupCalculations,Sample001.orbitalCalculations,Sample001.matrixCertificate,Sample001.densityComputed⟩
  centerBox := fun a => by
    change Sample000.localBox a = _
    rw [Sample000.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 0) (callBox (HighJet.tileCall 0 i))
      Sample000.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 0 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 0 i)) x :=
  tileEvaluation_actual 0 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile000
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
