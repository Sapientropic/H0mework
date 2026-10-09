import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor042.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile042
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample084.localBox,Sample084.localReductions,Sample084.material,Sample084.matrixRows,Sample084.densityRows⟩
  hull := ⟨Sample085.localBox,Sample085.localReductions,Sample085.material,Sample085.matrixRows,Sample085.densityRows⟩

theorem center_source : Sample084.center = HighJet.center 42 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample085.localBox = HighJet.tileBox 42 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 42 evaluation where
  center := ⟨Sample084.groupCalculations,Sample084.orbitalCalculations,Sample084.matrixCertificate,Sample084.densityComputed⟩
  hull := ⟨Sample085.groupCalculations,Sample085.orbitalCalculations,Sample085.matrixCertificate,Sample085.densityComputed⟩
  centerBox := fun a => by
    change Sample084.localBox a = _
    rw [Sample084.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 42) (callBox (HighJet.tileCall 42 i))
      Sample084.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 42 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 42 i)) x :=
  tileEvaluation_actual 42 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile042
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
