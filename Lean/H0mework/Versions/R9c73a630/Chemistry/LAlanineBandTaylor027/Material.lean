import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor027.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile027
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample054.localBox,Sample054.localReductions,Sample054.material,Sample054.matrixRows,Sample054.densityRows⟩
  hull := ⟨Sample055.localBox,Sample055.localReductions,Sample055.material,Sample055.matrixRows,Sample055.densityRows⟩

theorem center_source : Sample054.center = HighJet.center 27 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample055.localBox = HighJet.tileBox 27 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 27 evaluation where
  center := ⟨Sample054.groupCalculations,Sample054.orbitalCalculations,Sample054.matrixCertificate,Sample054.densityComputed⟩
  hull := ⟨Sample055.groupCalculations,Sample055.orbitalCalculations,Sample055.matrixCertificate,Sample055.densityComputed⟩
  centerBox := fun a => by
    change Sample054.localBox a = _
    rw [Sample054.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 27) (callBox (HighJet.tileCall 27 i))
      Sample054.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 27 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 27 i)) x :=
  tileEvaluation_actual 27 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile027
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
