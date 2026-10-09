import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.NetErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem pointer_sub (A B : PointerJoint) :
    Prepared.pointerReadout A-Prepared.pointerReadout B=Prepared.pointerReadout (A-B) := rfl
private theorem donor_sub (A B : Current.FullJoint) :
    Supply.donorSlice A-Supply.donorSlice B=Supply.donorSlice (A-B) := rfl

theorem root_corner_error : ‖Prepared.pointerReadout PCExecution.rootNet-Prepared.pointerReadout rootNet‖ ≤ (9/10^17 : ℝ) := by
  rw [pointer_sub]
  exact (Prepared.pointer_readout_norm _ (PCExecution.root_net_hermitian.sub root_net_hermitian)).trans root_net_error

theorem loaded_net_error : ‖PCExecution.loadedNet-loadedNet‖ ≤ (9/10^16 : ℝ) := by
  have hermitian := (Supply.raw_pullback_hermitian PCExecution.supply _
    (Prepared.pointer_readout_hermitian _ PCExecution.root_net_hermitian)).sub
      (Supply.raw_pullback_hermitian PCExecution.supply _ (Prepared.pointer_readout_hermitian _ root_net_hermitian))
  have same : PCExecution.loadedNet-loadedNet=Supply.donorSlice
      (star PCExecution.supply*(Prepared.pointerReadout PCExecution.rootNet)*PCExecution.supply-
        star PCExecution.supply*(Prepared.pointerReadout rootNet)*PCExecution.supply) := donor_sub _ _
  rw [same]
  apply (Post.donor_slice_norm _ hermitian).trans
  rw [← Matrix.sub_mul,← Matrix.mul_sub]
  exact (Prepared.sandwich_norm PCExecution.supply _).trans ((mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) PCExecution.supply_norm 2) root_corner_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem loaded_net_norm : ‖loadedNet‖ ≤ 163 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.loaded_net_norm loaded_net_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
