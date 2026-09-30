import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor031.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile031
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample062.localBox,Sample062.localReductions,Sample062.material,Sample062.matrixRows,Sample062.densityRows⟩
  hull := ⟨Sample063.localBox,Sample063.localReductions,Sample063.material,Sample063.matrixRows,Sample063.densityRows⟩

theorem center_source : Sample062.center = HighJet.center 31 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample063.localBox = HighJet.tileBox 31 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 31 evaluation where
  center := ⟨Sample062.groupCalculations,Sample062.orbitalCalculations,Sample062.matrixCertificate,Sample062.densityComputed⟩
  hull := ⟨Sample063.groupCalculations,Sample063.orbitalCalculations,Sample063.matrixCertificate,Sample063.densityComputed⟩
  centerBox := fun a => by
    change Sample062.localBox a = _
    rw [Sample062.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 31) (callBox (HighJet.tileCall 31 i))
      Sample062.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 31 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 31 i)) x :=
  tileEvaluation_actual 31 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile031
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
