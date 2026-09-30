import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor028.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile028
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample056.localBox,Sample056.localReductions,Sample056.material,Sample056.matrixRows,Sample056.densityRows⟩
  hull := ⟨Sample057.localBox,Sample057.localReductions,Sample057.material,Sample057.matrixRows,Sample057.densityRows⟩

theorem center_source : Sample056.center = HighJet.center 28 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample057.localBox = HighJet.tileBox 28 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 28 evaluation where
  center := ⟨Sample056.groupCalculations,Sample056.orbitalCalculations,Sample056.matrixCertificate,Sample056.densityComputed⟩
  hull := ⟨Sample057.groupCalculations,Sample057.orbitalCalculations,Sample057.matrixCertificate,Sample057.densityComputed⟩
  centerBox := fun a => by
    change Sample056.localBox a = _
    rw [Sample056.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 28) (callBox (HighJet.tileCall 28 i))
      Sample056.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 28 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 28 i)) x :=
  tileEvaluation_actual 28 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile028
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
