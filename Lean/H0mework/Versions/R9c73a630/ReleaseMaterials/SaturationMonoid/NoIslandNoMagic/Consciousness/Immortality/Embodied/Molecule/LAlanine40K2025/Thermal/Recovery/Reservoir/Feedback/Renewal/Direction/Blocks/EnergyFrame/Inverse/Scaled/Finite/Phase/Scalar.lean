import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open Propagation.Producer
noncomputable section

def pointerPhase : ℂ := ((sineHat^2-cosineHat^2 : ℝ) : ℂ)-Complex.I*((2*cosineHat*sineHat : ℝ) : ℂ)

theorem original_phase_components : (freePhase (nativeClockStep : ℝ) : ℂ)=
    (((Real.sin BasisInverse.actualAngle)^2-(Real.cos BasisInverse.actualAngle)^2 : ℝ) : ℂ)-
      Complex.I*((2*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle : ℝ) : ℂ) := by
  change NormedSpace.exp (-Complex.I*2*(nativeClockStep : ℂ))=_
  rw [← Complex.exp_eq_exp_ℂ]
  have angle : -Complex.I*2*(nativeClockStep : ℂ)=((-2*(nativeClockStep : ℝ) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [angle,Complex.exp_ofReal_mul_I,BasisInverse.actualAngle,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  simp only [neg_mul,Real.cos_neg,Real.sin_neg,Real.cos_two_mul,Real.sin_two_mul]
  push_cast
  linear_combination Complex.sin_sq_add_cos_sq (nativeClockStep : ℂ)

theorem original_phase_error : ‖(freePhase (nativeClockStep : ℝ) : ℂ)-pointerPhase‖ ≤ (12/10^18 : ℝ) := by
  have realError : |((Real.sin BasisInverse.actualAngle)^2-(Real.cos BasisInverse.actualAngle)^2)-(sineHat^2-cosineHat^2)| ≤ (6/10^18 : ℝ) := by
    have h := abs_sub ((Real.sin BasisInverse.actualAngle)^2-sineHat^2) ((Real.cos BasisInverse.actualAngle)^2-cosineHat^2)
    have same : ((Real.sin BasisInverse.actualAngle)^2-(Real.cos BasisInverse.actualAngle)^2)-(sineHat^2-cosineHat^2)=
        ((Real.sin BasisInverse.actualAngle)^2-sineHat^2)-((Real.cos BasisInverse.actualAngle)^2-cosineHat^2) := by ring
    rw [same]
    exact h.trans (by linarith [sine_square_error,cosine_square_error])
  have imagError : |2*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-2*cosineHat*sineHat| ≤ (6/10^18 : ℝ) := by
    rw [show 2*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-2*cosineHat*sineHat=
      2*(Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-cosineHat*sineHat) by ring,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [sine_cosine_error]
  rw [original_phase_components,pointerPhase]
  have split (x y u v : ℝ) : ((x : ℂ)-Complex.I*y)-((u : ℂ)-Complex.I*v)=((x-u : ℝ) : ℂ)-Complex.I*((y-v : ℝ) : ℂ) := by push_cast; ring
  rw [split]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
