import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor058.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile058
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample116.localBox,Sample116.localReductions,Sample116.material,Sample116.matrixRows,Sample116.densityRows⟩
  hull := ⟨Sample117.localBox,Sample117.localReductions,Sample117.material,Sample117.matrixRows,Sample117.densityRows⟩

theorem center_source : Sample116.center = HighJet.center 58 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample117.localBox = HighJet.tileBox 58 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 58 evaluation where
  center := ⟨Sample116.groupCalculations,Sample116.orbitalCalculations,Sample116.matrixCertificate,Sample116.densityComputed⟩
  hull := ⟨Sample117.groupCalculations,Sample117.orbitalCalculations,Sample117.matrixCertificate,Sample117.densityComputed⟩
  centerBox := fun a => by
    change Sample116.localBox a = _
    rw [Sample116.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 58) (callBox (HighJet.tileCall 58 i))
      Sample116.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 58 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 58 i)) x :=
  tileEvaluation_actual 58 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile058
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
