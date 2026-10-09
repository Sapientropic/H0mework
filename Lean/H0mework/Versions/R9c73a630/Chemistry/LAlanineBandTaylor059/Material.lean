import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor059.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile059
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample118.localBox,Sample118.localReductions,Sample118.material,Sample118.matrixRows,Sample118.densityRows⟩
  hull := ⟨Sample119.localBox,Sample119.localReductions,Sample119.material,Sample119.matrixRows,Sample119.densityRows⟩

theorem center_source : Sample118.center = HighJet.center 59 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample119.localBox = HighJet.tileBox 59 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 59 evaluation where
  center := ⟨Sample118.groupCalculations,Sample118.orbitalCalculations,Sample118.matrixCertificate,Sample118.densityComputed⟩
  hull := ⟨Sample119.groupCalculations,Sample119.orbitalCalculations,Sample119.matrixCertificate,Sample119.densityComputed⟩
  centerBox := fun a => by
    change Sample118.localBox a = _
    rw [Sample118.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 59) (callBox (HighJet.tileCall 59 i))
      Sample118.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 59 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 59 i)) x :=
  tileEvaluation_actual 59 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile059
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
