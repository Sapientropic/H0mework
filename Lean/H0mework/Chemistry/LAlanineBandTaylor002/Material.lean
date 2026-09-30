import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor002.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile002
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample004.localBox,Sample004.localReductions,Sample004.material,Sample004.matrixRows,Sample004.densityRows⟩
  hull := ⟨Sample005.localBox,Sample005.localReductions,Sample005.material,Sample005.matrixRows,Sample005.densityRows⟩

theorem center_source : Sample004.center = HighJet.center 2 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample005.localBox = HighJet.tileBox 2 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 2 evaluation where
  center := ⟨Sample004.groupCalculations,Sample004.orbitalCalculations,Sample004.matrixCertificate,Sample004.densityComputed⟩
  hull := ⟨Sample005.groupCalculations,Sample005.orbitalCalculations,Sample005.matrixCertificate,Sample005.densityComputed⟩
  centerBox := fun a => by
    change Sample004.localBox a = _
    rw [Sample004.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 2) (callBox (HighJet.tileCall 2 i))
      Sample004.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 2 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 2 i)) x :=
  tileEvaluation_actual 2 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile002
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
