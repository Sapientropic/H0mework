import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.BaseErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem root_rotation_error (R : LoadedJoint) (bounded : ‖R‖ ≤ 2) :
    ‖Post.rotatedRoot R-rotatedRoot R‖ ≤ (1/10^22 : ℝ) := by
  have p := Post.raw_sandwich_change (star Phase.freePolynomial) (star free) R
  simp only [star_star,norm_star,← star_sub] at p
  exact p.trans ((mul_le_mul (mul_le_mul (add_le_add original_free_norm free_norm) bounded
    (norm_nonneg _) (by norm_num)) free_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_root_rotation_error (R : LoadedJoint) (bounded : ‖R‖ ≤ 2) :
    ‖Incidence.bodyObservable (Post.rotatedRoot R)-Incidence.bodyObservable (rotatedRoot R)‖ ≤ (1/10^22 : ℝ) := by
  rw [← bodyObservable_sub]
  exact (body_observable_norm _).trans (root_rotation_error R bounded)

theorem pointer_error : ‖Post.finiteSourcePointer-pointer‖ ≤ (2/10^22 : ℝ) :=
  (SquareRoot.raw_dilation_error _ _ _ _).trans
    ((add_le_add (body_root_rotation_error SquareRoot.Full.sourceRoot Post.source_roots_norm.1)
      (body_root_rotation_error SquareRoot.Full.sourceComplement Post.source_roots_norm.2)).trans (by norm_num))

theorem pointer_norm : ‖pointer‖ ≤ 3 :=
  (close_norm _ _ _ _ Post.finite_source_pointer_norm pointer_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
