import H0mework.Physics.SpinPair.KineticLoad
import H0mework.Physics.SpinPair.CoframeCalculus

/-! The original matter coframe derivative on the shared actual. The full
load and the genuine inverse-coframe derivative generate all sixteen entries. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeVariation
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineEnrichedProofFreeSource
open scoped Matrix.Norms.Elementwise

noncomputable section

private abbrev Source := positiveSmoothUnifiedSource

private theorem actual_inverseLoad_zero (point : BasePoint) :
    inverseLoad (actualKineticLoad point) (actual.coframe point) = 0 := by
  have value : generatedDensitizedContinuumMatterKineticDensity Source 0 point
      (withCoframe (toContinuumPointField actual point) (actual.coframe point)) = 0 := by
    change generatedDensitizedContinuumMatterKineticDensity Source 0 point
      (toContinuumPointField actual point) = 0
    unfold generatedDensitizedContinuumMatterKineticDensity
    rw [actual_kineticVector_zero]
    simp
  rw [actual_frozenKineticDensity] at value
  change |(actual.coframe point).det| * inverseLoad (actualKineticLoad point) (actual.coframe point) = 0 at value
  exact (mul_eq_zero.mp value).resolve_left (abs_ne_zero.mpr (actual_nondegenerate point))

theorem actual_matterCoframe (point : BasePoint) (direction : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterEulerCovector Source point (toContinuumPointField actual point) direction =
      -6*(spinScale-gaugeScale)*spinScale*direction 0 0 +
        2*lapse*(spinScale-gaugeScale)*spinScale*(direction 1 1 + direction 2 2 + direction 3 3) := by
  have derivative := diracDualFormNativeCoframeMatterDensity_hasFDerivAt Source point
    (toContinuumPointField actual point) (actual_nondegenerate point)
  rw [show (toContinuumPointField actual point).coframe = actual.coframe point from rfl] at derivative
  have derivative' : HasFDerivAt
      (diracDualFormNativeCoframeMatterDensity Source point (toContinuumPointField actual point))
      (diracDualFormNativeCoframeMatterEulerCovector Source point (toContinuumPointField actual point))
      (actual.coframe point + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using derivative
  have evaluated := derivative'.comp_hasDerivAt 0 (coframe_line_hasDerivAt (actual.coframe point) direction)
  have computed : HasDerivAt
      (fun parameter : ℝ => diracDualFormNativeCoframeMatterDensity Source point
        (toContinuumPointField actual point) (actual.coframe point + parameter • direction))
      (|(actual.coframe point).det| * ∑ μ, ∑ a,
        (-(actual.coframe point)⁻¹ * direction * (actual.coframe point)⁻¹) μ a * actualKineticLoad point a μ) 0 := by
    simp_rw [actual_frozenMatterDensity]
    convert! volumeInverseLoad_line_hasDerivAt (actualKineticLoad point) (actual.coframe point) direction
      (actual_nondegenerate point) (actual_inverseLoad_zero point) using 1
    simp only [Matrix.neg_mul]
  have observed := evaluated.unique computed
  change diracDualFormNativeCoframeMatterEulerCovector Source point
    (toContinuumPointField actual point) direction = _ at observed
  rw [observed, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos,
    homogeneousCoframe_inv lapse (ne_of_gt lapse_pos), actualKineticLoad_diagonal]
  simp [homogeneousCoframe, Matrix.mul_apply, Fin.sum_univ_four]
  unfold frequency
  field_simp [ne_of_gt lapse_pos]
  ring

theorem actual_matterCoframe_coordinates (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeMatterEulerCovector Source point (toContinuumPointField actual point)
      (Matrix.single row column 1) =
      if row = column then
        if row = 0 then -6*(spinScale-gaugeScale)*spinScale
        else 2*lapse*(spinScale-gaugeScale)*spinScale
      else 0 := by
  rw [actual_matterCoframe]
  fin_cases row <;> fin_cases column <;> simp

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
