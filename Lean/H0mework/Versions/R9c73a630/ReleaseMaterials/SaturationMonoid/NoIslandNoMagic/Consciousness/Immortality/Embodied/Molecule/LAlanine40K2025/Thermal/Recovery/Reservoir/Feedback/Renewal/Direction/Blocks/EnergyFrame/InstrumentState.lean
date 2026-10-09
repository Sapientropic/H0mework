import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.RootConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerFreeContinuation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem root_norm_le_one (E : Matrix ι ι ℂ) (bounded : E ≤ 1) : ‖CFC.sqrt E‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CFC.sqrt_nonneg E)).mpr
  simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt E 1 bounded

theorem left_right_state_error (A B C D rho : Matrix ι ι ℂ)
    (left : ‖A‖ ≤ 1) (right : ‖D‖ ≤ 1) :
    ‖A*rho*C-B*rho*D‖ ≤ (‖A-B‖+‖C-D‖)*‖rho‖ := by
  have split : A*rho*C-B*rho*D = A*rho*(C-D)+(A-B)*rho*D := by noncomm_ring
  rw [split]
  calc
    _ ≤ ‖A*rho*(C-D)‖+‖(A-B)*rho*D‖ := norm_add_le _ _
    _ ≤ (‖A‖*‖rho‖)*‖C-D‖+(‖A-B‖*‖rho‖)*‖D‖ := by
      apply add_le_add <;> exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (1*‖rho‖)*‖C-D‖+(‖A-B‖*‖rho‖)*1 := by gcongr
    _ = _ := by ring

def branchRoot (A : Matrix ι ι ℂ) (selected : Bool) : Matrix ι ι ℂ :=
  if selected then effectRoot (boundedEffect A) else complementRoot (boundedEffect A)

theorem branch_root_norm (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (selected : Bool) :
    ‖branchRoot A selected‖ ≤ 1 := by
  have positive := (boundedEffect_positive A hermitian).nonneg
  have complement := (boundedEffect_complement_positive A hermitian).nonneg
  cases selected
  · exact root_norm_le_one _ (sub_le_self _ positive)
  · exact root_norm_le_one _ (sub_nonneg.mp complement)

theorem branch_root_error (A B : Matrix ι ι ℂ) (ha : A.IsHermitian) (hb : B.IsHermitian) (selected : Bool) :
    ‖branchRoot A selected-branchRoot B selected‖ ≤ rootErrorBudget A B := by
  cases selected
  · exact complement_root_error A B ha hb
  · exact effect_root_error A B ha hb

/-- Both diagonal branches and the retained off-diagonal pointer coherence satisfy the same error. -/
theorem instrument_block_error (A B rho : Matrix ι ι ℂ) (ha : A.IsHermitian) (hb : B.IsHermitian)
    (left right : Bool) :
    ‖branchRoot A left*rho*branchRoot A right-branchRoot B left*rho*branchRoot B right‖ ≤
      2*rootErrorBudget A B*‖rho‖ := by
  exact (left_right_state_error _ _ _ _ rho (branch_root_norm A ha left) (branch_root_norm B hb right)).trans
    (by gcongr; linarith [branch_root_error A B ha hb left,branch_root_error A B ha hb right])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
