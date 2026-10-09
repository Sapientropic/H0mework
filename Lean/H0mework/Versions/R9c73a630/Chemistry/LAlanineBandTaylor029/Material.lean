import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor029.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile029
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample058.localBox,Sample058.localReductions,Sample058.material,Sample058.matrixRows,Sample058.densityRows⟩
  hull := ⟨Sample059.localBox,Sample059.localReductions,Sample059.material,Sample059.matrixRows,Sample059.densityRows⟩

theorem center_source : Sample058.center = HighJet.center 29 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample059.localBox = HighJet.tileBox 29 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 29 evaluation where
  center := ⟨Sample058.groupCalculations,Sample058.orbitalCalculations,Sample058.matrixCertificate,Sample058.densityComputed⟩
  hull := ⟨Sample059.groupCalculations,Sample059.orbitalCalculations,Sample059.matrixCertificate,Sample059.densityComputed⟩
  centerBox := fun a => by
    change Sample058.localBox a = _
    rw [Sample058.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 29) (callBox (HighJet.tileCall 29 i))
      Sample058.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 29 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 29 i)) x :=
  tileEvaluation_actual 29 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile029
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
