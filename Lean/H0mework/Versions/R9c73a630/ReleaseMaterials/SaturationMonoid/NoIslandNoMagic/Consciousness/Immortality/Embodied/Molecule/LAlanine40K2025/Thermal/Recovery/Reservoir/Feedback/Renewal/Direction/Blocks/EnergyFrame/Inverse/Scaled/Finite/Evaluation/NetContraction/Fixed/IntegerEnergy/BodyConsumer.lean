import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.BodyLiteral
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem literal_first_body_table :
    toTable sourceFirstBodyInt pairFin pairFin=literalFirstBodyTable :=
  int_table_ext literal_first_body_re literal_first_body_im

theorem literal_first_body_original :
    fromTable literalFirstBodyTable pairFin pairFin=sourceFirstBodyInt := by
  rw [← literal_first_body_table]
  exact from_to_table _ _ _

theorem literal_first_body_source_error :
    ‖value (fromTable literalFirstBodyTable pairFin pairFin)-
      qvalue (qkron (ordinaryPairBlockQ (0 : Basis) (1 : Basis)) environmentQ)‖ ≤
      (64/10^30 : ℝ) := by
  rw [literal_first_body_original]
  exact quantize_error
    (qkron (ordinaryPairBlockQ (0 : Basis) (1 : Basis)) environmentQ)
    (by norm_num) (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
