import H0mework.Probability.SourceShift.Carrier
import H0mework.Realization.HilbertTransfer.Laplacian

/-! The same successor preserves the first-order square and generates a nonzero Laplacian residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.SourceShift

open IsometricRetainedTransfer

noncomputable section

def difference : H →L[ℂ] H := shift.toContinuousLinearMap - ContinuousLinearMap.id ℂ H

def laplacian : H →L[ℂ] H := difference.adjoint.comp difference

theorem difference_square : difference.comp shift.toContinuousLinearMap =
    shift.toContinuousLinearMap.comp difference := by
  apply ContinuousLinearMap.ext
  intro value
  change shift (shift value) - shift value = shift (shift value - value)
  exact (map_sub shift _ _).symm

theorem laplacian_formula (value : H) :
    laplacian value = value + value - shift value - transfer shift value := by
  change difference.adjoint (difference value) = _
  rw [difference, map_sub, ContinuousLinearMap.adjoint_id]
  change shift.toContinuousLinearMap.adjoint (shift value - value) - (shift value - value) = _
  rw [map_sub]
  have inverse : shift.toContinuousLinearMap.adjoint (shift value) = value := transfer_pullback shift value
  rw [inverse]
  change value - transfer shift value - (shift value - value) = _
  abel

theorem laplacian_shift_defect (value : H) :
    laplacian (shift value) - shift (laplacian value) = -residual shift value := by
  rw [laplacian_formula, laplacian_formula, transfer_pullback]
  simp only [map_add, map_sub]
  change _ = -(value - shift (transfer shift value))
  abel

theorem image_residual (value : H) :
    residual shift (laplacian (shift value)) = -residual shift value := by
  have decomposition := LaplacianRefinement.image_decomposition shift difference difference difference_square value
  change laplacian (shift value) = shift (laplacian value) + residual shift (laplacian (shift value))
    at decomposition
  have defect := laplacian_shift_defect value
  rw [decomposition, add_sub_cancel_left] at defect
  exact defect

theorem image_residual_basis_zero :
    residual shift (laplacian (shift (basis 0))) = -basis 0 := by
  rw [image_residual, residual_basis_zero]

theorem image_residual_ne_zero : residual shift (laplacian (shift (basis 0))) ≠ 0 := by
  rw [image_residual_basis_zero, neg_ne_zero]
  exact basis_zero_ne_zero

theorem laplacian_does_not_commute :
    laplacian (shift (basis 0)) ≠ shift (laplacian (basis 0)) := by
  intro commutes
  exact image_residual_ne_zero
    ((LaplacianRefinement.image_commutes_iff shift difference difference difference_square (basis 0)).mp commutes)

theorem second_image_has_zero_residual (value : H) :
    residual shift (laplacian (shift (shift value))) = 0 := by
  rw [image_residual, (residual_zero_iff shift (shift value)).mpr ⟨value, rfl⟩, neg_zero]

theorem retained_laplacian_image (value : H) :
    ‖laplacian (shift value)‖ ^ 2 = ‖laplacian value‖ ^ 2 + ‖residual shift value‖ ^ 2 := by
  have energy := LaplacianRefinement.image_energy shift difference difference difference_square value
  change ‖laplacian (shift value)‖ ^ 2 = ‖laplacian value‖ ^ 2 +
    ‖residual shift (laplacian (shift value))‖ ^ 2 at energy
  simpa only [image_residual, norm_neg] using energy

end
end SourceOwnedObservationHistory.SourceShift
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
