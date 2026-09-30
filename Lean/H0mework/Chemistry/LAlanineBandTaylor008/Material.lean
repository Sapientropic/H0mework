import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor008.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile008
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample016.localBox,Sample016.localReductions,Sample016.material,Sample016.matrixRows,Sample016.densityRows⟩
  hull := ⟨Sample017.localBox,Sample017.localReductions,Sample017.material,Sample017.matrixRows,Sample017.densityRows⟩

theorem center_source : Sample016.center = HighJet.center 8 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample017.localBox = HighJet.tileBox 8 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 8 evaluation where
  center := ⟨Sample016.groupCalculations,Sample016.orbitalCalculations,Sample016.matrixCertificate,Sample016.densityComputed⟩
  hull := ⟨Sample017.groupCalculations,Sample017.orbitalCalculations,Sample017.matrixCertificate,Sample017.densityComputed⟩
  centerBox := fun a => by
    change Sample016.localBox a = _
    rw [Sample016.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 8) (callBox (HighJet.tileCall 8 i))
      Sample016.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 8 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 8 i)) x :=
  tileEvaluation_actual 8 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile008
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
