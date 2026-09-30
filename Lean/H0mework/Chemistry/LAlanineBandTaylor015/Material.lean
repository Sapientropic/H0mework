import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor015.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile015
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample030.localBox,Sample030.localReductions,Sample030.material,Sample030.matrixRows,Sample030.densityRows⟩
  hull := ⟨Sample031.localBox,Sample031.localReductions,Sample031.material,Sample031.matrixRows,Sample031.densityRows⟩

theorem center_source : Sample030.center = HighJet.center 15 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample031.localBox = HighJet.tileBox 15 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 15 evaluation where
  center := ⟨Sample030.groupCalculations,Sample030.orbitalCalculations,Sample030.matrixCertificate,Sample030.densityComputed⟩
  hull := ⟨Sample031.groupCalculations,Sample031.orbitalCalculations,Sample031.matrixCertificate,Sample031.densityComputed⟩
  centerBox := fun a => by
    change Sample030.localBox a = _
    rw [Sample030.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 15) (callBox (HighJet.tileCall 15 i))
      Sample030.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 15 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 15 i)) x :=
  tileEvaluation_actual 15 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile015
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
