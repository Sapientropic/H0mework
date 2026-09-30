import H0mework.Chemistry.LAlanineBandMaterial.Tile
import H0mework.Chemistry.LAlanineBandTaylor048.TileActual

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile048
open SourceGaussianModel SourceSignedEvaluator WholeBandSource
noncomputable section

def evaluation : TileEvaluation where
  center := ⟨Sample096.localBox,Sample096.localReductions,Sample096.material,Sample096.matrixRows,Sample096.densityRows⟩
  hull := ⟨Sample097.localBox,Sample097.localReductions,Sample097.material,Sample097.matrixRows,Sample097.densityRows⟩

theorem center_source : Sample096.center = HighJet.center 48 := by
  funext a
  fin_cases a <;> decide +kernel

theorem hull_source : Sample097.localBox = HighJet.tileBox 48 := by
  funext a
  fin_cases a <;> decide +kernel

theorem evaluation_sound : TileEvaluationSound 48 evaluation where
  center := ⟨Sample096.groupCalculations,Sample096.orbitalCalculations,Sample096.matrixCertificate,Sample096.densityComputed⟩
  hull := ⟨Sample097.groupCalculations,Sample097.orbitalCalculations,Sample097.matrixCertificate,Sample097.densityComputed⟩
  centerBox := fun a => by
    change Sample096.localBox a = _
    rw [Sample096.center_box,center_source]
  hullBox := hull_source
  reports := fun i => by
    change HighJet.FieldWithin (Taylor.fieldEnclosure (HighJet.center 48) (callBox (HighJet.tileCall 48 i))
      Sample096.bounds fourthBounds) _
    rw [← center_source]
    exact all_reports i

theorem retained_material_actual (i : HighJet.Slot) (x : Point)
    (inside : InRectangle (callBox (HighJet.tileCall 48 i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall 48 i)) x :=
  tileEvaluation_actual 48 evaluation evaluation_sound i x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile048
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
