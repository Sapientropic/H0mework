import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor039.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile039
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample078.localBox,Sample078.localReductions,Sample078.material,Sample078.matrixRows,Sample078.densityRows⟩
  hull := ⟨Sample079.localBox,Sample079.localReductions,Sample079.material,Sample079.matrixRows,Sample079.densityRows⟩

theorem center_source : Sample078.center = HighJet.center 39 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample079.localBox = HighJet.tileBox 39 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 39 evaluation where
  center := ⟨Sample078.groupCalculations,Sample078.orbitalCalculations,Sample078.matrixCertificate,Sample078.densityComputed⟩
  hull := ⟨Sample079.groupCalculations,Sample079.orbitalCalculations,Sample079.matrixCertificate,Sample079.densityComputed⟩
  centerBox := fun a => by
    change Sample078.localBox a = _
    rw [Sample078.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 39) (callBox (HighJet.tileCall 39 i))
      Sample078.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 39 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 39 i)) x :=
  tileEvaluation_actual 39 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile039
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
