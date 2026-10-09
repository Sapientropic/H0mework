import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor000.TileData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile000
open WholeBandSource

theorem first_gradient (a : Fin 3) : HighJet.PairWithin
    ((restrictedField 0).gradient a) ((recordedCallField 0).gradient a) := by
  fin_cases a <;> decide +kernel

theorem first_hessian (a b : Fin 3) : HighJet.PairWithin
    ((restrictedField 0).hessian a b) ((recordedCallField 0).hessian a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem first_report : HighJet.FieldWithin (restrictedField 0) (recordedCallField 0) :=
  ⟨first_gradient,first_hessian⟩
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile000
