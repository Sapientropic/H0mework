import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Restrictions

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Collision Fixed
open scoped Matrix

private theorem multiply_swap (A : JointMatrix PairController) (c s : ℝ) :
    A*partialSwap c s=(c : ℂ) • A-(Complex.I*(s : ℂ)) • A.submatrix id Prod.swap := by
  rw [partialSwap,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.mul_smul]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,mul_swap_apply,Matrix.submatrix_apply,Prod.swap_prod_mk,id_eq]

theorem multiply_partialSwapQ (A : MatrixQ (PairController × PairController) (PairController × PairController)) (c s : ℚ) :
    qmultiply A (partialSwapQ PairController c s)=qscale (c,0) A+qscale (0,-s) (A.submatrix id Prod.swap) := by
  apply qvalue_injective
  rw [qvalue_multiply,partialSwapQ_value,multiply_swap,qvalue_add,qvalue_scale,qvalue_scale,qvalue_submatrix]
  ext i j
  simp only [Scalar.value,Rat.cast_zero,Rat.cast_neg,zero_add,mul_zero,add_zero,
    Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_ratCast]
  ring

def supplyEntriesQ : MatrixQ Current.FullIndex Current.FullIndex :=
  qkron (qscale (SquareRoot.Full.cosine,0) Spec.sharedPC+
    qscale (0,-SquareRoot.Full.sine) (Spec.sharedPC.submatrix id Prod.swap)) freeEnvironmentQ

def weakEntriesQ : MatrixQ Current.FullIndex Current.FullIndex :=
  qkron (qscale (SquareRoot.Full.sine,0) Spec.sharedPC+
    qscale (0,-SquareRoot.Full.cosine) (Spec.sharedPC.submatrix id Prod.swap)) freeEnvironmentQ

theorem supply_entries_exact : Spec.supply=supplyEntriesQ := by
  rw [Spec.supply,multiply_partialSwapQ]
  rfl

theorem weak_entries_exact : Spec.weak=weakEntriesQ := by
  rw [Spec.weak,multiply_partialSwapQ]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
