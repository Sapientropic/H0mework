import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor060.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile060
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample120.localBox,Sample120.localReductions,Sample120.material,Sample120.matrixRows,Sample120.densityRows⟩
  hull := ⟨Sample121.localBox,Sample121.localReductions,Sample121.material,Sample121.matrixRows,Sample121.densityRows⟩

theorem center_source : Sample120.center = HighJet.center 60 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample121.localBox = HighJet.tileBox 60 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 60 evaluation where
  center := ⟨Sample120.groupCalculations,Sample120.orbitalCalculations,Sample120.matrixCertificate,Sample120.densityComputed⟩
  hull := ⟨Sample121.groupCalculations,Sample121.orbitalCalculations,Sample121.matrixCertificate,Sample121.densityComputed⟩
  centerBox := fun a => by
    change Sample120.localBox a = _
    rw [Sample120.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 60) (callBox (HighJet.tileCall 60 i))
      Sample120.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 60 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 60 i)) x :=
  tileEvaluation_actual 60 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile060
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
