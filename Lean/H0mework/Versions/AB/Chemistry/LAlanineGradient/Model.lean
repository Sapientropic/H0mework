import H0mework.Versions.AB.Chemistry.LAlanineRefinementSource.FiniteData
import H0mework.Chemistry.LAlanineRefinementDensity.DensityModel
import H0mework.Chemistry.LAlanineGradient.Differential

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient

open SourceGaussianModel SourceFiniteData
open scoped BigOperators

noncomputable section

def zeroJet : MultiIndex := fun _ => 0

def sourceDensity : Point → ℝ := density sourceTerms densityMatrix

def sourceGradient (x : Point) (axis : Fin 3) : ℝ :=
  firstBilinear sourceTerms densityMatrix zeroJet zeroJet axis x

def sourceHessian (x : Point) (axis direction : Fin 3) : ℝ :=
  firstBilinear sourceTerms densityMatrix (raise zeroJet axis) zeroJet direction x +
    firstBilinear sourceTerms densityMatrix zeroJet (raise zeroJet axis) direction x

theorem sourceDensity_contDiff (order : WithTop ℕ∞) :
    ContDiff ℝ order sourceDensity :=
  bilinear_contDiff sourceTerms densityMatrix zeroJet zeroJet order

theorem sourceGradient_contDiff (order : WithTop ℕ∞) :
    ContDiff ℝ order sourceGradient := by
  apply contDiff_pi.mpr
  intro axis
  exact (bilinear_contDiff sourceTerms densityMatrix (raise zeroJet axis) zeroJet order).add
    (bilinear_contDiff sourceTerms densityMatrix zeroJet (raise zeroJet axis) order)

theorem sourceDensity_coordinate_derivative (x : Point) (axis : Fin 3) :
    HasDerivAt (fun t => sourceDensity (Function.update x axis t))
      (sourceGradient x axis) (x axis) :=
  bilinear_coordinate_derivative sourceTerms densityMatrix zeroJet zeroJet x axis

theorem sourceGradient_coordinate_derivative (x : Point) (axis direction : Fin 3) :
    HasDerivAt (fun t => sourceGradient (Function.update x direction t) axis)
      (sourceHessian x axis direction) (x direction) :=
  (bilinear_coordinate_derivative sourceTerms densityMatrix (raise zeroJet axis) zeroJet x direction).add
    (bilinear_coordinate_derivative sourceTerms densityMatrix zeroJet (raise zeroJet axis) x direction)

def sourceDensityLinear (x : Point) : Point →L[ℝ] ℝ :=
  ∑ axis : Fin 3, sourceGradient x axis • ContinuousLinearMap.proj axis

def sourceHessianLinear (x : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun axis =>
    ∑ direction : Fin 3, sourceHessian x axis direction • ContinuousLinearMap.proj direction)

theorem sourceDensity_hasFDerivAt (x : Point) :
    HasFDerivAt sourceDensity (sourceDensityLinear x) x := by
  have hd := (sourceDensity_contDiff 1).differentiable (by norm_num) x
  have he : fderiv ℝ sourceDensity x = sourceDensityLinear x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [linear_apply_coordinates]
    simp only [sourceDensityLinear, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro axis _
    rw [fderiv_coordinate sourceDensity x axis hd _ (sourceDensity_coordinate_derivative x axis)]
  rw [← he]
  exact hd.hasFDerivAt

theorem sourceHessianLinear_apply (x v : Point) (axis : Fin 3) :
    sourceHessianLinear x v axis = ∑ direction : Fin 3, sourceHessian x axis direction * v direction := by
  simp only [sourceHessianLinear, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem sourceGradient_hasFDerivAt (x : Point) :
    HasFDerivAt sourceGradient (sourceHessianLinear x) x := by
  change HasFDerivAt (fun y axis => sourceGradient y axis)
    (ContinuousLinearMap.pi (fun axis =>
      ∑ direction : Fin 3, sourceHessian x axis direction • ContinuousLinearMap.proj direction)) x
  apply hasFDerivAt_pi.mpr
  intro axis
  have hd : DifferentiableAt ℝ (fun y => sourceGradient y axis) x :=
    ((contDiff_pi.mp (sourceGradient_contDiff 1) axis).differentiable (by norm_num)) x
  have he : fderiv ℝ (fun y => sourceGradient y axis) x =
      ∑ direction : Fin 3, sourceHessian x axis direction • ContinuousLinearMap.proj direction := by
    apply ContinuousLinearMap.ext
    intro v
    rw [linear_apply_coordinates]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro direction _
    rw [fderiv_coordinate _ x direction hd _ (sourceGradient_coordinate_derivative x axis direction)]
  rw [← he]
  exact hd.hasFDerivAt

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient
