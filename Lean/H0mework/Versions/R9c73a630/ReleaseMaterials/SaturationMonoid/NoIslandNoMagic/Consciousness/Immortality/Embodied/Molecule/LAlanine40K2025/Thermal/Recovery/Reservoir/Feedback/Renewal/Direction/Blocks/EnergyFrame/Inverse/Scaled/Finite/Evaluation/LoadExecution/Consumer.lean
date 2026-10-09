import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.BodyErrors
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.ReadoutErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem energy_difference {ι : Type*} [Fintype ι] (O P A B : Matrix ι ι ℂ) :
    Collision.energy O A-Collision.energy P B=Collision.energy (O-P) A+Collision.energy P (A-B) := by
  simp only [Collision.energy,Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  ring

theorem load_computation_net_cost : |PCExecution.netGain-netGain| ≤ (1/10^8 : ℝ) := by
  have read : PCExecution.netGain-netGain=Collision.energy (PCExecution.loadedNet-loadedNet) PCExecution.receivedBody+
      Collision.energy loadedNet (PCExecution.receivedBody-receivedBody) :=
    energy_difference PCExecution.loadedNet loadedNet PCExecution.receivedBody receivedBody
  rw [read]
  have first := Input.energy_dimension_norm (PCExecution.loadedNet-loadedNet) PCExecution.receivedBody
  have second := Input.energy_dimension_norm loadedNet (PCExecution.receivedBody-receivedBody)
  have card : Fintype.card (PairController × Fin 2)=38416 := by norm_num [PairController,Basis]
  rw [card] at first second
  norm_num only [Nat.cast_ofNat] at first second
  have a := first.trans (mul_le_mul (mul_le_mul_of_nonneg_left loaded_net_error (by norm_num : (0 : ℝ) ≤ 38416)) old_body_norm (norm_nonneg _) (by norm_num))
  have b := second.trans (mul_le_mul (mul_le_mul_of_nonneg_left loaded_net_norm (by norm_num : (0 : ℝ) ≤ 38416)) body_error (norm_nonneg _) (by norm_num))
  exact (abs_add_le _ _).trans ((add_le_add a b).trans (by norm_num))

theorem original_computed_load_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-netGain| ≤
      (108/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) PCExecution.netGain netGain
  linarith [PCExecution.original_computed_pc_net_error,load_computation_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
