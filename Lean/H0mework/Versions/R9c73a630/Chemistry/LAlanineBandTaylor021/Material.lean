import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor021.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile021
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample042.localBox,Sample042.localReductions,Sample042.material,Sample042.matrixRows,Sample042.densityRows⟩
  hull := ⟨Sample043.localBox,Sample043.localReductions,Sample043.material,Sample043.matrixRows,Sample043.densityRows⟩

theorem center_source : Sample042.center = HighJet.center 21 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample043.localBox = HighJet.tileBox 21 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 21 evaluation where
  center := ⟨Sample042.groupCalculations,Sample042.orbitalCalculations,Sample042.matrixCertificate,Sample042.densityComputed⟩
  hull := ⟨Sample043.groupCalculations,Sample043.orbitalCalculations,Sample043.matrixCertificate,Sample043.densityComputed⟩
  centerBox := fun a => by
    change Sample042.localBox a = _
    rw [Sample042.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 21) (callBox (HighJet.tileCall 21 i))
      Sample042.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 21 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 21 i)) x :=
  tileEvaluation_actual 21 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile021
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
