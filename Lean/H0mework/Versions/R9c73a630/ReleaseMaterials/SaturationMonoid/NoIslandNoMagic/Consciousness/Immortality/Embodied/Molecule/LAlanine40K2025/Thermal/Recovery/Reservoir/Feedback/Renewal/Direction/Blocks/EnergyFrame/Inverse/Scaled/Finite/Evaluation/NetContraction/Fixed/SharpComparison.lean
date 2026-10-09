import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SpecNet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.PureDonor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
open Collision Load.Source
noncomputable section

theorem original_rational_net_error_sharp :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
        Resource.pcEnergyOf (bodyRead Weak.origin.joint)) - (netGain : ℝ)| ≤
      (80/10^7 : ℝ) := by
  rw [netGain_value]
  let originalNet : ℝ := Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
    Resource.pcEnergyOf (bodyRead Weak.origin.joint)
  change |originalNet - InputProducts.netGain| ≤ _
  have t1 := abs_sub_le originalNet Supply.finiteDonorNetGain
    Supply.finiteSupplyNetGain
  have t2 := abs_sub_le originalNet Supply.finiteSupplyNetGain Post.finiteNetGain
  have t3 := abs_sub_le originalNet Post.finiteNetGain Diagonal.computedNetGain
  have t4 := abs_sub_le originalNet Diagonal.computedNetGain Field.computedNetGain
  have t5 := abs_sub_le originalNet Field.computedNetGain PCExecution.netGain
  have t6 := abs_sub_le originalNet PCExecution.netGain LoadExecution.netGain
  have t7 := abs_sub_le originalNet LoadExecution.netGain InputProducts.netGain
  have first : |originalNet - Supply.finiteDonorNetGain| ≤ (79/10^7 : ℝ) :=
    Supply.original_finite_donor_net_error_sharp
  linarith [first,Supply.finite_supply_energy_cost,Post.finite_post_energy_cost,
    Diagonal.diagonal_computation_net_cost,Field.field_computation_net_cost,
    PCExecution.pc_computation_net_cost,LoadExecution.load_computation_net_cost,
    InputProducts.input_products_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
