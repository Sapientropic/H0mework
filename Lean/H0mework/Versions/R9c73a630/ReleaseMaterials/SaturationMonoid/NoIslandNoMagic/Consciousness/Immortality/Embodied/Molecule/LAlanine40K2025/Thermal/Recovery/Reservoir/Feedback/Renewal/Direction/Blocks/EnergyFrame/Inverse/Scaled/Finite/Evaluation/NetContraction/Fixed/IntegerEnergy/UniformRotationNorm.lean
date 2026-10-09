import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformRootConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Multiply
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Embedding
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem ordinary_orbit_pc_injective (a b : Basis) (ordered : a < b) :
    Function.Injective (orbitPC a b) := by
  intro i j h
  exact (offDiagonalEquiv a b ordered.ne).injective (Subtype.ext h)

theorem ordinary_free_norm_six (a b : Basis) (ordered : a < b) :
    ‖qvalue (qkron (onePCQ a b ordered) freeEnvironmentQ)‖ ≤ (6 : ℝ) := by
  rw [qvalue_kron,onePCQ_value,freeEnvironmentQ_value]
  have pc : ‖Primitive.computedPC.submatrix (orbitPC a b) (orbitPC a b)‖ ≤
      (3 : ℝ) :=
    (submatrix_norm_le Primitive.computedPC _ _
      (ordinary_orbit_pc_injective a b ordered)
      (ordinary_orbit_pc_injective a b ordered)).trans PCExecution.computed_pc_norm
  exact (kronecker_norm_le _ _).trans
    ((mul_le_mul pc PCExecution.original_environment_norm (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 3)).trans (by norm_num))

theorem ordinary_free_quantize_error (a b : Basis) (ordered : a < b) :
    ‖value (quantize (qkron (onePCQ a b ordered) freeEnvironmentQ))-
      qvalue (qkron (onePCQ a b ordered) freeEnvironmentQ)‖ ≤
      (1/10^25 : ℝ) :=
  (quantize_error _ (by norm_num [LoadPrimitive.NativeIndex])
    (by norm_num [LoadPrimitive.NativeIndex])).trans (by norm_num)

private theorem gram_norm_four {A B : Matrix (Fin 8) (Fin 8) ℚ}
    (G : SquareRoot.RootGram A B) (hF : ‖qvalue (factorQ G)‖ ≤ (2 : ℝ)) :
    ‖qvalue (rootGramQ G)‖ ≤ (4 : ℝ) := by
  let F := qvalue (factorQ G)
  have same : qvalue (rootGramQ G)=F*star F := by
    change qvalue (qmultiply (factorQ G) (qadjoint (factorQ G))) = _
    rw [qvalue_multiply,qvalue_adjoint]
    rfl
  rw [same]
  exact (norm_mul_le F (star F)).trans (by
    rw [norm_star]
    have h := mul_le_mul hF hF (norm_nonneg F) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h])

theorem ordinary_root_norms_four (a b : Basis) (ordered : a < b) :
    ‖qvalue (rootOrdinaryQ a b ordered)‖ ≤ (4 : ℝ) ∧
    ‖qvalue (complementOrdinaryQ a b ordered)‖ ≤ (4 : ℝ) := by
  have factors := source_ordinary_factor_norms_two a b ordered
  constructor
  · rw [rootOrdinaryQ,qvalue_submatrix,Finite.reindex_norm]
    exact gram_norm_four _ factors.1
  · rw [complementOrdinaryQ,qvalue_submatrix,Finite.reindex_norm]
    exact gram_norm_four _ factors.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
