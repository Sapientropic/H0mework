import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor043.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile043
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample086.localBox,Sample086.localReductions,Sample086.material,Sample086.matrixRows,Sample086.densityRows⟩
  hull := ⟨Sample087.localBox,Sample087.localReductions,Sample087.material,Sample087.matrixRows,Sample087.densityRows⟩

theorem center_source : Sample086.center = HighJet.center 43 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample087.localBox = HighJet.tileBox 43 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 43 evaluation where
  center := ⟨Sample086.groupCalculations,Sample086.orbitalCalculations,Sample086.matrixCertificate,Sample086.densityComputed⟩
  hull := ⟨Sample087.groupCalculations,Sample087.orbitalCalculations,Sample087.matrixCertificate,Sample087.densityComputed⟩
  centerBox := fun a => by
    change Sample086.localBox a = _
    rw [Sample086.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 43) (callBox (HighJet.tileCall 43 i))
      Sample086.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 43 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 43 i)) x :=
  tileEvaluation_actual 43 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile043
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
