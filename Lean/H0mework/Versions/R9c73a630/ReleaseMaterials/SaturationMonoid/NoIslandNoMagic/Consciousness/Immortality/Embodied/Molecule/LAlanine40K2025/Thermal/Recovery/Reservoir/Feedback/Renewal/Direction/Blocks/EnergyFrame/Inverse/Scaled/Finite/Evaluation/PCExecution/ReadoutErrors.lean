import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.NetErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem pointer_readout_sub (A B : PointerJoint) :
    Prepared.pointerReadout A-Prepared.pointerReadout B=Prepared.pointerReadout (A-B) := rfl

private theorem donor_readout_sub (A B : Current.FullJoint) :
    Supply.donorSlice A-Supply.donorSlice B=Supply.donorSlice (A-B) := rfl

theorem root_corner_error : ‖Prepared.pointerReadout Post.finiteRootNet-Prepared.pointerReadout rootNet‖ ≤ (3/10^16 : ℝ) := by
  have same : Prepared.pointerReadout Post.finiteRootNet-Prepared.pointerReadout rootNet=Prepared.pointerReadout (Post.finiteRootNet-rootNet) := pointer_readout_sub _ _
  rw [same]
  exact (Prepared.pointer_readout_norm _ (Post.finite_root_net_hermitian.sub root_net_hermitian)).trans root_net_error

theorem old_root_corner_norm : ‖Prepared.pointerReadout Post.finiteRootNet‖ ≤ 4 := by
  have root : ‖Post.finiteRootNet‖ ≤ 4 :=
    (Prepared.sandwich_norm Post.finiteSourcePointer Post.finiteNetObservable).trans
      ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) Post.finite_source_pointer_norm 2)
        Diagonal.finite_net_observable_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (Prepared.pointer_readout_norm _ Post.finite_root_net_hermitian).trans root

theorem loaded_net_error : ‖Post.finiteLoadedNet-loadedNet‖ ≤ (3/10^15 : ℝ) := by
  have oldHermitian := Supply.raw_pullback_hermitian Supply.fullSupplyPolynomial _
    (Prepared.pointer_readout_hermitian _ Post.finite_root_net_hermitian)
  have newHermitian := Supply.raw_pullback_hermitian supply _ (Prepared.pointer_readout_hermitian _ root_net_hermitian)
  have same : Post.finiteLoadedNet-loadedNet=Supply.donorSlice
      (star Supply.fullSupplyPolynomial*(Prepared.pointerReadout Post.finiteRootNet)*Supply.fullSupplyPolynomial-
        star supply*(Prepared.pointerReadout rootNet)*supply) := donor_readout_sub _ _
  rw [same]
  apply (Post.donor_slice_norm _ (oldHermitian.sub newHermitian)).trans
  have paid := raw_pair_pullback Supply.fullSupplyPolynomial supply (Prepared.pointerReadout Post.finiteRootNet) (Prepared.pointerReadout rootNet)
  exact paid.trans ((add_le_add
    (mul_le_mul (mul_le_mul (add_le_add Post.finite_full_supply_norm supply_norm) old_root_corner_norm
      (norm_nonneg _) (by norm_num)) supply_error (norm_nonneg _) (by norm_num))
    (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) supply_norm 2) root_corner_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem loaded_net_norm : ‖loadedNet‖ ≤ 162 := by
  have corner := (Prepared.pointer_readout_norm _ root_net_hermitian).trans root_net_norm
  have hermitian := Supply.raw_pullback_hermitian supply _ (Prepared.pointer_readout_hermitian _ root_net_hermitian)
  exact (Post.donor_slice_norm _ hermitian).trans ((Prepared.sandwich_norm supply _).trans
    ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) supply_norm 2) corner (norm_nonneg _) (by norm_num)).trans (by norm_num)))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
