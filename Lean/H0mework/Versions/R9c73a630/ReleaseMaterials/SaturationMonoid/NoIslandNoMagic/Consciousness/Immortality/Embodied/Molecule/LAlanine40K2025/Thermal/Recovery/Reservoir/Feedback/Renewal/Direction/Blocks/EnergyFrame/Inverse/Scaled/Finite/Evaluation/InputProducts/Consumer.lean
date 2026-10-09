import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def netGain : ℝ := Collision.energy LoadExecution.loadedNet body

private theorem energy_state_difference {ι : Type*} [Fintype ι] (O A B : Matrix ι ι ℂ) :
    Collision.energy O A-Collision.energy O B=Collision.energy O (A-B) := by
  simp only [Collision.energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]

theorem input_products_net_cost : |LoadExecution.netGain-netGain| ≤ (1/10^8 : ℝ) := by
  have same : LoadExecution.netGain-netGain=Collision.energy LoadExecution.loadedNet (LoadExecution.receivedBody-body) :=
    energy_state_difference _ _ _
  rw [same]
  have h := Input.energy_dimension_norm LoadExecution.loadedNet (LoadExecution.receivedBody-body)
  have card : Fintype.card (PairController × Fin 2)=38416 := by norm_num [PairController,Basis]
  rw [card] at h
  norm_num only [Nat.cast_ofNat] at h
  exact h.trans ((mul_le_mul (mul_le_mul_of_nonneg_left LoadExecution.loaded_net_norm (by norm_num : (0 : ℝ) ≤ 38416))
    body_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem original_computed_input_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-netGain| ≤
      (109/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) LoadExecution.netGain netGain
  linarith [LoadExecution.original_computed_load_net_error,input_products_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
