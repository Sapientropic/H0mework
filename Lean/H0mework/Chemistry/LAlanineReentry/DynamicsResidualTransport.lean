import H0mework.Chemistry.LAlanineReentry.RuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Continuation

open Propagation.Interface LAlanine40K2025.Reentry.Runtime
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def duration : ℚ := Propagation.Producer.nativeClockStep
def targetClock : ℚ := reentryParentTime + duration

theorem targetClock_exact : targetClock = 3 * Propagation.Producer.nativeClockStep := by
  rw [targetClock, reentryParent_clock]
  unfold duration
  ring

variable (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (C : Matrix Basis Basis ℂ)

def exactTarget : Matrix Basis Basis ℂ :=
  JointNext.Math.electronicAdvance H hermitian (duration : ℝ) C reentryParentHeld

def numericalInputTarget : Matrix Basis Basis ℂ :=
  JointNext.Math.electronicAdvance H hermitian (duration : ℝ) C reentryParentRealization.1

def inheritedResidual : Matrix Basis Basis ℂ :=
  JointNext.Math.electronicAdvance H hermitian (duration : ℝ) C reentryParentResidual

theorem inheritedResidual_exact (close : ‖C - 1‖ < 1) :
    numericalInputTarget H hermitian C - exactTarget H hermitian C = inheritedResidual H hermitian C := by
  unfold numericalInputTarget exactTarget inheritedResidual
  rw [JointNext.Math.electronicAdvance_joint H hermitian _ C _ close,
    JointNext.Math.electronicAdvance_joint H hermitian _ C _ close,
    JointNext.Math.electronicAdvance_joint H hermitian _ C _ close, ← map_sub,
    reentryParent_residual]

theorem inheritedResidual_norm (close : ‖C - 1‖ < 1) :
    ‖inheritedResidual H hermitian C‖ = ‖reentryParentResidual‖ := by
  unfold inheritedResidual
  rw [JointNext.Math.electronicAdvance_joint H hermitian _ C _ close]
  exact StarAlgEquiv.norm_map _ _

theorem inheritedResidual_bound (close : ‖C - 1‖ < 1) :
    ‖inheritedResidual H hermitian C‖ < (1 : ℝ) / 10 ^ 8 := by
  rw [inheritedResidual_norm H hermitian C close]
  exact reentryParent_error

/-- The new source output adds its own discrepancy to the transported entire previous discrepancy. -/
theorem totalResidual_reconstruction (close : ‖C - 1‖ < 1) (realized : Matrix Basis Basis ℂ) :
    realized - exactTarget H hermitian C = inheritedResidual H hermitian C +
      (realized - numericalInputTarget H hermitian C) := by
  rw [← inheritedResidual_exact H hermitian C close]
  abel

theorem totalResidual_bound (close : ‖C - 1‖ < 1) (realized : Matrix Basis Basis ℂ) :
    ‖realized - exactTarget H hermitian C‖ ≤ ‖reentryParentResidual‖ +
      ‖realized - numericalInputTarget H hermitian C‖ := by
  rw [totalResidual_reconstruction H hermitian C close realized]
  exact (norm_add_le _ _).trans_eq (by rw [inheritedResidual_norm H hermitian C close])

end
end LAlanine40K2025.Reentry.Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
