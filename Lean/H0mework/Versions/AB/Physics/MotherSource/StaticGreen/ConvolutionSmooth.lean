import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Convolution

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped ContDiff
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

def convolutionLinear (left right : MultiIndex) (position : Point) : Point →L[ℝ] ℝ :=
  ∑ axis : Fin 3, (densityConvolution (raise left axis) right position +
    densityConvolution left (raise right axis) position) • ContinuousLinearMap.proj axis

theorem convolution_first_integrable (left right : MultiIndex) (position : Point) (axis : Fin 3) :
    Integrable (fun point : Point => firstBilinear sourceTerms densityMatrix left right axis (position-point)*kernel point) := by
  have result := (convolution_integrable (raise left axis) right position).add
    (convolution_integrable left (raise right axis) position)
  convert result using 1 <;> try rfl
  funext point
  simp only [firstBilinear, Pi.add_apply, add_mul]

theorem convolution_first_integral (left right : MultiIndex) (position : Point) (axis : Fin 3) :
    (∫ point : Point, firstBilinear sourceTerms densityMatrix left right axis (position-point)*kernel point) =
      densityConvolution (raise left axis) right position + densityConvolution left (raise right axis) position := by
  simp only [firstBilinear, add_mul]
  rw [integral_add (convolution_integrable (raise left axis) right position)
    (convolution_integrable left (raise right axis) position)]
  rfl

theorem convolutionDerivative_sum (left right : MultiIndex) (position point : Point) :
    convolutionDerivative left right position point =
      ∑ axis : Fin 3, (firstBilinear sourceTerms densityMatrix left right axis (position-point)*kernel point) • ContinuousLinearMap.proj axis := by
  unfold convolutionDerivative bilinearLinear
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  rw [smul_smul, mul_comm]

theorem convolutionDerivative_integral (left right : MultiIndex) (position : Point) :
    (∫ point : Point, convolutionDerivative left right position point) = convolutionLinear left right position := by
  simp_rw [convolutionDerivative_sum]
  rw [integral_finsetSum Finset.univ (fun axis _ => (convolution_first_integrable left right position axis).smul_const _)]
  simp only [integral_smul_const, convolution_first_integral, convolutionLinear]

theorem convolution_hasFDerivAt (left right : MultiIndex) (position : Point) :
    HasFDerivAt (densityConvolution left right) (convolutionLinear left right position) position := by
  rw [← convolutionDerivative_integral]
  exact densityConvolution_hasFDerivAt left right position

theorem convolution_contDiff_nat (order : ℕ) (left right : MultiIndex) :
    ContDiff ℝ order (densityConvolution left right) := by
  induction order generalizing left right with
  | zero =>
    exact contDiff_zero.mpr (Differentiable.continuous
      (fun position => (convolution_hasFDerivAt left right position).differentiableAt))
  | succ order induction =>
    change ContDiff ℝ ((order : WithTop ℕ∞)+1) (densityConvolution left right)
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun position => (convolution_hasFDerivAt left right position).differentiableAt, ?_, ?_⟩
    · simp
    · have derivative : fderiv ℝ (densityConvolution left right) = convolutionLinear left right :=
        funext fun position => (convolution_hasFDerivAt left right position).fderiv
      rw [derivative]
      unfold convolutionLinear
      apply ContDiff.sum
      intro axis _
      exact ((induction (raise left axis) right).add (induction left (raise right axis))).smul contDiff_const

theorem convolution_smooth (left right : MultiIndex) : ContDiff ℝ ∞ (densityConvolution left right) :=
  contDiff_infty.mpr (fun order => convolution_contDiff_nat order left right)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
