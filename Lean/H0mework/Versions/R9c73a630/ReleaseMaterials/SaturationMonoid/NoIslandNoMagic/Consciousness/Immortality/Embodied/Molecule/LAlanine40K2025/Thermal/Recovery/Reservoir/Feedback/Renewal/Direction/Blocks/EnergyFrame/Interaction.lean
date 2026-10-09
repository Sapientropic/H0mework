import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Load.Producer.StrictThermal
open Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem difference_sub (H K : Matrix Basis Basis ℂ) : difference H-difference K = difference (H-K) := by
  ext i j
  simp only [difference,Matrix.sub_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
  ring

theorem source_difference_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖difference H-difference K‖ ≤ 2*‖H-K‖ := by
  rw [difference_sub]
  unfold difference
  calc
    _ ≤ ‖Matrix.kronecker (H-K) 1‖+‖Matrix.kronecker 1 (H-K)‖ := norm_sub_le _ _
    _ ≤ ‖H-K‖+‖H-K‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le tensorLeft _)
      (NonUnitalStarAlgHom.norm_apply_le tensorRight _)
    _ = _ := by ring

private theorem raising_sub (H K : Matrix Basis Basis ℂ) :
    raising H-raising K = (1/2 : ℂ) • ((difference H-difference K)+swapOperator*(difference H-difference K)) := by
  simp only [raising,smul_sub,mul_sub,smul_add]
  abel

theorem source_raising_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖raising H-raising K‖ ≤ 2*‖H-K‖ := by
  rw [raising_sub,norm_smul]
  have swapBound : ‖(swapOperator : JointMatrix Basis)*(difference H-difference K)‖ ≤ ‖difference H-difference K‖ := by
    simpa only [swap_norm,one_mul] using norm_mul_le (swapOperator : JointMatrix Basis) (difference H-difference K)
  have sumBound := norm_add_le (difference H-difference K) (swapOperator*(difference H-difference K))
  norm_num
  linarith [source_difference_perturbation H K]

theorem source_interaction_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖interaction H-interaction K‖ ≤ 4*‖H-K‖ := by
  have delta : interaction H-interaction K = (transfer H-transfer K)+(transfer H-transfer K)ᴴ := by
    simp only [interaction,Matrix.conjTranspose_sub]
    abel
  have transferDelta : transfer H-transfer K = Matrix.kronecker (raising H-raising K) lowering := by
    ext i j
    simp only [transfer,Matrix.sub_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  have transferBound : ‖transfer H-transfer K‖ ≤ 2*‖H-K‖ := by
    rw [transferDelta]
    apply (kronecker_norm_le _ _).trans
    have lower := sourceLowering_norm_le
    have raise := source_raising_perturbation H K
    nlinarith [norm_nonneg (raising H-raising K),norm_nonneg lowering]
  rw [delta]
  have bound := norm_add_le (transfer H-transfer K) (transfer H-transfer K)ᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at bound
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
