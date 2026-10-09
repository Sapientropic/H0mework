import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.TraceNorm
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedOrdinaryPairBlock (a b : Basis) : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)

theorem computed_ordinary_pair_positive (a b : Basis) :
    (computedOrdinaryPairBlock a b).PosSemidef := by
  exact computed_pair_positive.submatrix (pairAddress a b)

theorem source_ordinary_pair_block_error (a b : Basis) (ordered : a < b) :
    ‖originalPairBlock a b-computedOrdinaryPairBlock a b‖ ≤
      (2/10^20 : ℝ) := by
  have injective := source_ordinary_pair_address_injective a b ordered
  change ‖(InputProducts.pair-Field.computedPair).submatrix
    (pairAddress a b) (pairAddress a b)‖ ≤ _
  have h := (submatrix_norm_le (Field.computedPair-InputProducts.pair)
    (pairAddress a b) (pairAddress a b) injective injective).trans
    InputProducts.pair_error
  change ‖Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)-
    InputProducts.pair.submatrix (pairAddress a b) (pairAddress a b)‖ ≤ _ at h
  change ‖InputProducts.pair.submatrix (pairAddress a b) (pairAddress a b)-
    Field.computedPair.submatrix (pairAddress a b) (pairAddress a b)‖ ≤ _
  rw [norm_sub_rev]
  exact h

theorem source_ordinary_pair_norm_by_mass (a b : Basis) (ordered : a < b) :
    ‖originalPairBlock a b‖ ≤
      (computedOrdinaryPairBlock a b).trace.re+(2/10^20 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (originalPairBlock a b) (computedOrdinaryPairBlock a b) 0
  simp only [sub_zero] at triangle
  have mass := positive_norm_le_trace_re (computedOrdinaryPairBlock a b)
    (computed_ordinary_pair_positive a b)
  linarith only [triangle,source_ordinary_pair_block_error a b ordered,mass]

theorem source_ordinary_body_norm_by_mass (a b : Basis) (ordered : a < b) :
    ‖qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ ≤
      2*((computedOrdinaryPairBlock a b).trace.re+(2/10^20 : ℝ)) := by
  rw [qvalue_kron,ordinary_pair_block_value,environmentQ_value]
  have nonnegative : (0 : ℝ) ≤
      (computedOrdinaryPairBlock a b).trace.re+(2/10^20 : ℝ) :=
    (norm_nonneg (originalPairBlock a b)).trans
      (source_ordinary_pair_norm_by_mass a b ordered)
  exact (kronecker_norm_le _ _).trans
    ((mul_le_mul (source_ordinary_pair_norm_by_mass a b ordered)
      Diagonal.finite_environment_norm (norm_nonneg _) nonnegative).trans (by nlinarith))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
