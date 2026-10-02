import H0mework.Versions.R2.Physics.SourceCoframe.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe

open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeVariation
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineEnrichedProofFreeSource
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem inverse_load_zero (step : ℕ) (point : BasePoint) :
    inverseLoad (kineticLoad step point) ((fieldAt step).coframe point) = 0 := by
  have value : generatedDensitizedContinuumMatterKineticDensity (sourceAt step) 0 point
      (withCoframe (toContinuumPointField (fieldAt step) point) ((fieldAt step).coframe point)) = 0 := by
    change generatedDensitizedContinuumMatterKineticDensity (sourceAt step) 0 point
      (toContinuumPointField (fieldAt step) point) = 0
    unfold generatedDensitizedContinuumMatterKineticDensity
    rw [Dirac.kinetic_zero]
    simp
  rw [frozen_kinetic_density] at value
  change |((fieldAt step).coframe point).det| *
    inverseLoad (kineticLoad step point) ((fieldAt step).coframe point) = 0 at value
  exact (mul_eq_zero.mp value).resolve_left (abs_ne_zero.mpr (field_nondegenerate step point))

theorem matter_coframe (step : ℕ) (point : BasePoint) (direction : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) direction =
      -6*(spinScale-gaugeScale)*spinScale*direction 0 0 +
        2*clock step*(spinScale-gaugeScale)*spinScale*(direction 1 1 + direction 2 2 + direction 3 3) := by
  have derivative := diracDualFormNativeCoframeMatterDensity_hasFDerivAt (sourceAt step) point
    (toContinuumPointField (fieldAt step) point) (field_nondegenerate step point)
  rw [show (toContinuumPointField (fieldAt step) point).coframe = (fieldAt step).coframe point from rfl]
    at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeMatterDensity (sourceAt step) point (toContinuumPointField (fieldAt step) point))
      (diracDualFormNativeCoframeMatterEulerCovector (sourceAt step) point
        (toContinuumPointField (fieldAt step) point))
      ((fieldAt step).coframe point + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using derivative
  have evaluated := derivative'.comp_hasDerivAt 0
    (coframe_line_hasDerivAt ((fieldAt step).coframe point) direction)
  have computed : HasDerivAt
      (fun parameter : ℝ => diracDualFormNativeCoframeMatterDensity (sourceAt step) point
        (toContinuumPointField (fieldAt step) point) ((fieldAt step).coframe point + parameter • direction))
      (|((fieldAt step).coframe point).det| * ∑ μ, ∑ a,
        (-((fieldAt step).coframe point)⁻¹ * direction * ((fieldAt step).coframe point)⁻¹) μ a *
          kineticLoad step point a μ) 0 := by
    simp_rw [frozen_matter_density]
    convert! volumeInverseLoad_line_hasDerivAt (kineticLoad step point) ((fieldAt step).coframe point) direction
      (field_nondegenerate step point) (inverse_load_zero step point) using 1
    simp only [Matrix.neg_mul]
  have observed := evaluated.unique computed
  change diracDualFormNativeCoframeMatterEulerCovector (sourceAt step) point
    (toContinuumPointField (fieldAt step) point) direction = _ at observed
  rw [observed, field_coframe, homogeneousCoframe_det, abs_of_pos (clock_pos step),
    homogeneousCoframe_inv (clock step) (ne_of_gt (clock_pos step)), kinetic_load_diagonal]
  simp [homogeneousCoframe, Matrix.mul_apply, Fin.sum_univ_four]
  unfold phaseRate
  field_simp [ne_of_gt (clock_pos step)]
  ring

theorem matter_coordinates (step : ℕ) (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeMatterEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) (Matrix.single row column 1) =
      if row = column then
        if row = 0 then -6*(spinScale-gaugeScale)*spinScale
        else 2*clock step*(spinScale-gaugeScale)*spinScale
      else 0 := by
  rw [matter_coframe]
  fin_cases row <;> fin_cases column <;> simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe
