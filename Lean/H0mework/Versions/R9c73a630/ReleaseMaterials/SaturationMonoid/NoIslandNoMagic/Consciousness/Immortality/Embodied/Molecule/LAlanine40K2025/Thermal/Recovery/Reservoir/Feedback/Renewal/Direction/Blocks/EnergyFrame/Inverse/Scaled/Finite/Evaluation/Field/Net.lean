import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedNetGain : ℝ := Collision.energy Post.finiteLoadedNet computedBody

private theorem energy_input_sub {ι : Type*} [Fintype ι] (O A B : Matrix ι ι ℂ) :
    Collision.energy O A-Collision.energy O B=Collision.energy O (A-B) := by
  simp only [Collision.energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]

theorem field_computation_net_cost : |Diagonal.computedNetGain-computedNetGain| ≤ (1/10^8 : ℝ) := by
  have read : Diagonal.computedNetGain-computedNetGain=Collision.energy Post.finiteLoadedNet (Diagonal.computedBody-computedBody) :=
    energy_input_sub Post.finiteLoadedNet Diagonal.computedBody computedBody
  rw [read]
  have paid := Input.energy_dimension_norm Post.finiteLoadedNet (Diagonal.computedBody-computedBody)
  have cardinal : Fintype.card (PairController × Fin 2)=38416 := by norm_num [PairController,Basis]
  rw [cardinal] at paid
  norm_num only [Nat.cast_ofNat] at paid
  exact paid.trans ((mul_le_mul (mul_le_mul_of_nonneg_left Diagonal.final_observable_norm
    (show (0 : ℝ) ≤ 38416 by norm_num)) body_numeric_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem original_computed_field_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-computedNetGain| ≤
      (106/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) Diagonal.computedNetGain computedNetGain
  linarith [Diagonal.original_computed_diagonal_net_error,field_computation_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
