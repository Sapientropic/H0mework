import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor018.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile018
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample036.localBox,Sample036.localReductions,Sample036.material,Sample036.matrixRows,Sample036.densityRows⟩
  hull := ⟨Sample037.localBox,Sample037.localReductions,Sample037.material,Sample037.matrixRows,Sample037.densityRows⟩

theorem center_source : Sample036.center = HighJet.center 18 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample037.localBox = HighJet.tileBox 18 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 18 evaluation where
  center := ⟨Sample036.groupCalculations,Sample036.orbitalCalculations,Sample036.matrixCertificate,Sample036.densityComputed⟩
  hull := ⟨Sample037.groupCalculations,Sample037.orbitalCalculations,Sample037.matrixCertificate,Sample037.densityComputed⟩
  centerBox := fun a => by
    change Sample036.localBox a = _
    rw [Sample036.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 18) (callBox (HighJet.tileCall 18 i))
      Sample036.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 18 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 18 i)) x :=
  tileEvaluation_actual 18 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile018
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
