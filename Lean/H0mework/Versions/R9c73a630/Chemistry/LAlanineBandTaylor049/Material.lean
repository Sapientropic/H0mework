import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor049.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile049
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample098.localBox,Sample098.localReductions,Sample098.material,Sample098.matrixRows,Sample098.densityRows⟩
  hull := ⟨Sample099.localBox,Sample099.localReductions,Sample099.material,Sample099.matrixRows,Sample099.densityRows⟩

theorem center_source : Sample098.center = HighJet.center 49 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample099.localBox = HighJet.tileBox 49 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 49 evaluation where
  center := ⟨Sample098.groupCalculations,Sample098.orbitalCalculations,Sample098.matrixCertificate,Sample098.densityComputed⟩
  hull := ⟨Sample099.groupCalculations,Sample099.orbitalCalculations,Sample099.matrixCertificate,Sample099.densityComputed⟩
  centerBox := fun a => by
    change Sample098.localBox a = _
    rw [Sample098.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 49) (callBox (HighJet.tileCall 49 i))
      Sample098.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 49 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 49 i)) x :=
  tileEvaluation_actual 49 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile049
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
