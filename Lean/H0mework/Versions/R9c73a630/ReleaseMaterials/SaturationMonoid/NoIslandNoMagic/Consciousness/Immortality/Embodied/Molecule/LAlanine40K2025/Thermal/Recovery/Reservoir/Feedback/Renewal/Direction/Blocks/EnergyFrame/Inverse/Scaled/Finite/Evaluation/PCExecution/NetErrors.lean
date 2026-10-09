import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.SuffixErrors
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.RootErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem difference_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℂ) :
    ‖(A-B)-(C-D)‖ ≤ ‖A-C‖+‖B-D‖ := by
  have split : (A-B)-(C-D)=(A-C)-(B-D) := by abel
  rw [split]
  exact norm_sub_le _ _

theorem net_observable_error : ‖Post.finiteNetObservable-netObservable‖ ≤ (3/10^17 : ℝ) := by
  have first := Post.raw_sandwich_change Post.elevenPolynomial eleven Post.finitePCObservable
  have second := Post.raw_sandwich_change Post.ninePolynomial nine Post.finitePCObservable
  have firstBound := first.trans (mul_le_mul (mul_le_mul (add_le_add old_eleven_norm eleven_norm)
    Post.finite_PC_observable_norm (norm_nonneg _) (by norm_num)) eleven_error (norm_nonneg _) (by norm_num))
  have secondBound := second.trans (mul_le_mul (mul_le_mul (add_le_add old_nine_norm nine_norm)
    Post.finite_PC_observable_norm (norm_nonneg _) (by norm_num)) nine_error (norm_nonneg _) (by norm_num))
  exact (difference_norm _ _ _ _).trans ((add_le_add firstBound secondBound).trans (by norm_num))

theorem net_observable_norm : ‖netObservable‖ ≤ 2 :=
  (close_norm _ _ _ _ Diagonal.finite_net_observable_norm net_observable_error).trans (by norm_num)

theorem root_net_error : ‖Post.finiteRootNet-rootNet‖ ≤ (3/10^16 : ℝ) :=
  (raw_pair_pullback Post.finiteSourcePointer pointer Post.finiteNetObservable netObservable).trans ((add_le_add
    (mul_le_mul (mul_le_mul (add_le_add Post.finite_source_pointer_norm pointer_norm)
      Diagonal.finite_net_observable_norm (norm_nonneg _) (by norm_num)) pointer_error (norm_nonneg _) (by norm_num))
    (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) pointer_norm 2) net_observable_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem net_observable_hermitian : netObservable.IsHermitian :=
  (Supply.raw_pullback_hermitian _ _ Post.finite_PC_observable_hermitian).sub
    (Supply.raw_pullback_hermitian _ _ Post.finite_PC_observable_hermitian)

theorem root_net_hermitian : rootNet.IsHermitian := Supply.raw_pullback_hermitian _ _ net_observable_hermitian

theorem root_net_norm : ‖rootNet‖ ≤ 18 :=
  (Prepared.sandwich_norm pointer netObservable).trans ((mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) pointer_norm 2) net_observable_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
