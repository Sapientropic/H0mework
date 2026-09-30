import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor005.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile005
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample010.localBox,Sample010.localReductions,Sample010.material,Sample010.matrixRows,Sample010.densityRows⟩
  hull := ⟨Sample011.localBox,Sample011.localReductions,Sample011.material,Sample011.matrixRows,Sample011.densityRows⟩

theorem center_source : Sample010.center = HighJet.center 5 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample011.localBox = HighJet.tileBox 5 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 5 evaluation where
  center := ⟨Sample010.groupCalculations,Sample010.orbitalCalculations,Sample010.matrixCertificate,Sample010.densityComputed⟩
  hull := ⟨Sample011.groupCalculations,Sample011.orbitalCalculations,Sample011.matrixCertificate,Sample011.densityComputed⟩
  centerBox := fun a => by
    change Sample010.localBox a = _
    rw [Sample010.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 5) (callBox (HighJet.tileCall 5 i))
      Sample010.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 5 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 5 i)) x :=
  tileEvaluation_actual 5 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile005
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
