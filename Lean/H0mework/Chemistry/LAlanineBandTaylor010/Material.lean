import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor010.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile010
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample020.localBox,Sample020.localReductions,Sample020.material,Sample020.matrixRows,Sample020.densityRows⟩
  hull := ⟨Sample021.localBox,Sample021.localReductions,Sample021.material,Sample021.matrixRows,Sample021.densityRows⟩

theorem center_source : Sample020.center = HighJet.center 10 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample021.localBox = HighJet.tileBox 10 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 10 evaluation where
  center := ⟨Sample020.groupCalculations,Sample020.orbitalCalculations,Sample020.matrixCertificate,Sample020.densityComputed⟩
  hull := ⟨Sample021.groupCalculations,Sample021.orbitalCalculations,Sample021.matrixCertificate,Sample021.densityComputed⟩
  centerBox := fun a => by
    change Sample020.localBox a = _
    rw [Sample020.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 10) (callBox (HighJet.tileCall 10 i))
      Sample020.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 10 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 10 i)) x :=
  tileEvaluation_actual 10 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile010
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
