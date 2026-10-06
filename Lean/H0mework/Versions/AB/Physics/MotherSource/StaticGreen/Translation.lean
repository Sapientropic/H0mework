import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Green

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open Stage9C.Material.SpinPair
noncomputable section

def translate (centre : Point) : 𝓢(Point, ℝ) →L[ℝ] 𝓢(Point, ℝ) :=
  SchwartzMap.compCLM ℝ (g := fun point : Point => point+centre) (by fun_prop) (by
    refine ⟨1, 1+‖centre‖, fun point => ?_⟩
    have bound := norm_sub_le (point+centre) centre
    simp only [add_sub_cancel_right, pow_one] at bound ⊢
    nlinarith [mul_nonneg (norm_nonneg centre) (norm_nonneg (point+centre))])

@[simp] theorem translate_apply (centre : Point) (test : 𝓢(Point, ℝ)) (point : Point) :
    translate centre test point = test (point+centre) := rfl

theorem translate_line (centre direction : Point) (test : 𝓢(Point, ℝ)) :
    ∂_{direction} (translate centre test) = translate centre (∂_{direction} test) := by
  ext point
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, translate_apply]
  change fderiv ℝ (fun p : Point => test (p+centre)) point direction = _
  have derivative := (test.hasFDerivAt (point+centre)).comp point
    ((hasFDerivAt_id point).add_const centre)
  have readout : fderiv ℝ (fun p : Point => test (p+centre)) point =
      (fderiv ℝ test (point+centre)).comp (ContinuousLinearMap.id ℝ Point) := derivative.fderiv
  rw [readout]
  rfl

theorem translate_laplacian (centre : Point) (test : 𝓢(Point, ℝ)) :
    testLaplacian (translate centre test) = translate centre (testLaplacian test) := by
  unfold testLaplacian
  simp only [translate_line, map_sum]

theorem green_shifted_fundamental (centre : Point) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, green (point-centre)*(-(2*lapse)*testLaplacian test point)) = test centre := by
  have result := green_fundamental (translate centre test)
  rw [translate_laplacian] at result
  simp only [translate_apply, zero_add] at result
  have shifted := integral_add_right_eq_self (μ := volume)
    (fun point : Point => green (point-centre)*(-(2*lapse)*testLaplacian test point)) centre
  simp only [add_sub_cancel_right] at shifted
  exact shifted.symm.trans result

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
