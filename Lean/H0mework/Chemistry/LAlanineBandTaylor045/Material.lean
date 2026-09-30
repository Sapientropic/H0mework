import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor045.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile045
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample090.localBox,Sample090.localReductions,Sample090.material,Sample090.matrixRows,Sample090.densityRows⟩
  hull := ⟨Sample091.localBox,Sample091.localReductions,Sample091.material,Sample091.matrixRows,Sample091.densityRows⟩

theorem center_source : Sample090.center = HighJet.center 45 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample091.localBox = HighJet.tileBox 45 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 45 evaluation where
  center := ⟨Sample090.groupCalculations,Sample090.orbitalCalculations,Sample090.matrixCertificate,Sample090.densityComputed⟩
  hull := ⟨Sample091.groupCalculations,Sample091.orbitalCalculations,Sample091.matrixCertificate,Sample091.densityComputed⟩
  centerBox := fun a => by
    change Sample090.localBox a = _
    rw [Sample090.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 45) (callBox (HighJet.tileCall 45 i))
      Sample090.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 45 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 45 i)) x :=
  tileEvaluation_actual 45 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile045
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
