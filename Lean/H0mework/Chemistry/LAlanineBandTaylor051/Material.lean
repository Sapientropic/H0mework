import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor051.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile051
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample102.localBox,Sample102.localReductions,Sample102.material,Sample102.matrixRows,Sample102.densityRows⟩
  hull := ⟨Sample103.localBox,Sample103.localReductions,Sample103.material,Sample103.matrixRows,Sample103.densityRows⟩

theorem center_source : Sample102.center = HighJet.center 51 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample103.localBox = HighJet.tileBox 51 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 51 evaluation where
  center := ⟨Sample102.groupCalculations,Sample102.orbitalCalculations,Sample102.matrixCertificate,Sample102.densityComputed⟩
  hull := ⟨Sample103.groupCalculations,Sample103.orbitalCalculations,Sample103.matrixCertificate,Sample103.densityComputed⟩
  centerBox := fun a => by
    change Sample102.localBox a = _
    rw [Sample102.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 51) (callBox (HighJet.tileCall 51 i))
      Sample102.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 51 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 51 i)) x :=
  tileEvaluation_actual 51 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile051
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
