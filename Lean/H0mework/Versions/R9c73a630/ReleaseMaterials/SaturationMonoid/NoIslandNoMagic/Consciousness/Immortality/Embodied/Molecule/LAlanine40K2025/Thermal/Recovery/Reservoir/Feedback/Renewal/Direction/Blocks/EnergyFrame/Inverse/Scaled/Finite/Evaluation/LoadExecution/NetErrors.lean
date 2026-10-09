import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.SuffixErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem difference_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℂ) :
    ‖(A-B)-(C-D)‖ ≤ ‖A-C‖+‖B-D‖ := by
  have same : (A-B)-(C-D)=(A-C)-(B-D) := by abel
  rw [same]
  exact norm_sub_le _ _

theorem net_observable_error : ‖PCExecution.netObservable-netObservable‖ ≤ (1/10^17 : ℝ) := by
  have first := Post.raw_sandwich_change PCExecution.eleven eleven Post.finitePCObservable
  have second := Post.raw_sandwich_change PCExecution.nine nine Post.finitePCObservable
  have a := first.trans (mul_le_mul (mul_le_mul (add_le_add PCExecution.eleven_norm eleven_norm)
    Post.finite_PC_observable_norm (norm_nonneg _) (by norm_num)) eleven_error (norm_nonneg _) (by norm_num))
  have b := second.trans (mul_le_mul (mul_le_mul (add_le_add PCExecution.nine_norm nine_norm)
    Post.finite_PC_observable_norm (norm_nonneg _) (by norm_num)) nine_error (norm_nonneg _) (by norm_num))
  exact (difference_norm _ _ _ _).trans ((add_le_add a b).trans (by norm_num))

theorem net_observable_hermitian : netObservable.IsHermitian :=
  (Supply.raw_pullback_hermitian _ _ Post.finite_PC_observable_hermitian).sub
    (Supply.raw_pullback_hermitian _ _ Post.finite_PC_observable_hermitian)

theorem root_net_hermitian : rootNet.IsHermitian := Supply.raw_pullback_hermitian _ _ net_observable_hermitian

private theorem sandwich_sub {ι : Type*} [Fintype ι] (P A B : Matrix ι ι ℂ) :
    star P*A*P-star P*B*P=star P*(A-B)*P := by
  rw [Matrix.mul_sub,Matrix.sub_mul]

theorem root_net_error : ‖PCExecution.rootNet-rootNet‖ ≤ (9/10^17 : ℝ) := by
  have same : PCExecution.rootNet-rootNet=star PCExecution.pointer*(PCExecution.netObservable-netObservable)*PCExecution.pointer := sandwich_sub _ _ _
  rw [same]
  exact (Prepared.sandwich_norm PCExecution.pointer _).trans ((mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) PCExecution.pointer_norm 2) net_observable_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
