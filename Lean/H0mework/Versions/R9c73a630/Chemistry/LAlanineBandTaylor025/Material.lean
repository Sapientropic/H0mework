import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor025.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile025
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample050.localBox,Sample050.localReductions,Sample050.material,Sample050.matrixRows,Sample050.densityRows⟩
  hull := ⟨Sample051.localBox,Sample051.localReductions,Sample051.material,Sample051.matrixRows,Sample051.densityRows⟩

theorem center_source : Sample050.center = HighJet.center 25 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample051.localBox = HighJet.tileBox 25 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 25 evaluation where
  center := ⟨Sample050.groupCalculations,Sample050.orbitalCalculations,Sample050.matrixCertificate,Sample050.densityComputed⟩
  hull := ⟨Sample051.groupCalculations,Sample051.orbitalCalculations,Sample051.matrixCertificate,Sample051.densityComputed⟩
  centerBox := fun a => by
    change Sample050.localBox a = _
    rw [Sample050.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 25) (callBox (HighJet.tileCall 25 i))
      Sample050.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 25 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 25 i)) x :=
  tileEvaluation_actual 25 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile025
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
