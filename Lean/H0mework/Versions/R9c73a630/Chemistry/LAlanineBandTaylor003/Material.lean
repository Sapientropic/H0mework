import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor003.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile003
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample006.localBox,Sample006.localReductions,Sample006.material,Sample006.matrixRows,Sample006.densityRows⟩
  hull := ⟨Sample007.localBox,Sample007.localReductions,Sample007.material,Sample007.matrixRows,Sample007.densityRows⟩

theorem center_source : Sample006.center = HighJet.center 3 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample007.localBox = HighJet.tileBox 3 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 3 evaluation where
  center := ⟨Sample006.groupCalculations,Sample006.orbitalCalculations,Sample006.matrixCertificate,Sample006.densityComputed⟩
  hull := ⟨Sample007.groupCalculations,Sample007.orbitalCalculations,Sample007.matrixCertificate,Sample007.densityComputed⟩
  centerBox := fun a => by
    change Sample006.localBox a = _
    rw [Sample006.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 3) (callBox (HighJet.tileCall 3 i))
      Sample006.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 3 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 3 i)) x :=
  tileEvaluation_actual 3 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile003
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
