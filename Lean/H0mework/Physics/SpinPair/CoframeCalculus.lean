import H0mework.Physics.Homogeneous.CoframeDifferential

/-! The original volume and inverse-coframe derivatives contract with a
fixed kinetic load. A zero kinetic value removes the volume-derivative term. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineCoframeVariation
open Stage9C.Dynamics.Homogeneous
open scoped Matrix.Norms.Elementwise

noncomputable section

def inverseLoad (load candidate : LorentzianCoframe) : ℝ :=
  ∑ direction, ∑ spin, candidate⁻¹ direction spin * load spin direction

theorem inverseLoad_line_hasDerivAt (load coframe direction : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    HasDerivAt (fun parameter : ℝ => inverseLoad load (coframe + parameter • direction))
      (∑ μ, ∑ a, (-(coframe⁻¹ * direction * coframe⁻¹)) μ a * load a μ) 0 := by
  have inverse := coframeInverse_line_hasDerivAt coframe direction nondegenerate
  have entry (μ a : LorentzianIndex) :
      HasDerivAt (fun parameter : ℝ => (coframe + parameter • direction)⁻¹ μ a)
        (-(coframe⁻¹ * direction * coframe⁻¹) μ a) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp inverse μ) a
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => (entry μ a).mul_const (load a μ)))

theorem volumeInverseLoad_line_hasDerivAt
    (load coframe direction : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) (onShell : inverseLoad load coframe = 0) :
    HasDerivAt
      (fun parameter : ℝ => abs (Matrix.det (coframe + parameter • direction)) *
        inverseLoad load (coframe + parameter • direction))
      (abs (Matrix.det coframe) *
        ∑ μ, ∑ a, (-(coframe⁻¹ * direction * coframe⁻¹)) μ a * load a μ) 0 := by
  have volume := ((coframe_volume_contDiffAt (coframe + (0 : ℝ) • direction)
    (by simpa only [zero_smul, add_zero] using nondegenerate)).differentiableAt (by simp)).hasFDerivAt
  have volumeLine := volume.comp_hasDerivAt 0 (coframe_line_hasDerivAt coframe direction)
  have product := volumeLine.mul (inverseLoad_line_hasDerivAt load coframe direction nondegenerate)
  convert! product using 1
  simp only [Function.comp_apply, zero_smul, add_zero, onShell, mul_zero, zero_add]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
