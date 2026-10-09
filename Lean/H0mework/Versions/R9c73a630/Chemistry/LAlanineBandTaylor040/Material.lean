import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor040.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile040
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample080.localBox,Sample080.localReductions,Sample080.material,Sample080.matrixRows,Sample080.densityRows⟩
  hull := ⟨Sample081.localBox,Sample081.localReductions,Sample081.material,Sample081.matrixRows,Sample081.densityRows⟩

theorem center_source : Sample080.center = HighJet.center 40 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample081.localBox = HighJet.tileBox 40 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 40 evaluation where
  center := ⟨Sample080.groupCalculations,Sample080.orbitalCalculations,Sample080.matrixCertificate,Sample080.densityComputed⟩
  hull := ⟨Sample081.groupCalculations,Sample081.orbitalCalculations,Sample081.matrixCertificate,Sample081.densityComputed⟩
  centerBox := fun a => by
    change Sample080.localBox a = _
    rw [Sample080.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 40) (callBox (HighJet.tileCall 40 i))
      Sample080.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 40 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 40 i)) x :=
  tileEvaluation_actual 40 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile040
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
