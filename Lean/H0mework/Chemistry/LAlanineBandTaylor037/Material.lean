import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor037.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile037
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample074.localBox,Sample074.localReductions,Sample074.material,Sample074.matrixRows,Sample074.densityRows⟩
  hull := ⟨Sample075.localBox,Sample075.localReductions,Sample075.material,Sample075.matrixRows,Sample075.densityRows⟩

theorem center_source : Sample074.center = HighJet.center 37 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample075.localBox = HighJet.tileBox 37 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 37 evaluation where
  center := ⟨Sample074.groupCalculations,Sample074.orbitalCalculations,Sample074.matrixCertificate,Sample074.densityComputed⟩
  hull := ⟨Sample075.groupCalculations,Sample075.orbitalCalculations,Sample075.matrixCertificate,Sample075.densityComputed⟩
  centerBox := fun a => by
    change Sample074.localBox a = _
    rw [Sample074.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 37) (callBox (HighJet.tileCall 37 i))
      Sample074.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 37 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 37 i)) x :=
  tileEvaluation_actual 37 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile037
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
