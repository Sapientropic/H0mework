import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.ConvolutionRegularity

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter Metric
open scoped Topology
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

def densityConvolution (left right : MultiIndex) (position : Point) : ℝ :=
  ∫ point : Point, bilinear sourceTerms densityMatrix left right (position-point)*kernel point

theorem convolution_integrable (left right : MultiIndex) (position : Point) :
    Integrable (fun point : Point => bilinear sourceTerms densityMatrix left right (position-point)*kernel point) :=
  integrable_mul_kernel _ ((source_bilinear_integrable left right).comp_sub_left position)
    (sourceBilinearBound left right) (fun point => source_bilinear_uniform_bound left right (position-point))

theorem bilinearLinear_continuous (left right : MultiIndex) : Continuous (bilinearLinear left right) := by
  unfold bilinearLinear
  apply continuous_finsetSum
  intro axis _
  exact (((bilinear_contDiff sourceTerms densityMatrix (raise left axis) right 0).continuous).add
    ((bilinear_contDiff sourceTerms densityMatrix left (raise right axis) 0).continuous)).smul continuous_const

def convolutionDerivative (left right : MultiIndex) (position point : Point) : Point →L[ℝ] ℝ :=
  kernel point • bilinearLinear left right (position-point)

theorem integrand_hasFDerivAt (left right : MultiIndex) (position point : Point) :
    HasFDerivAt (fun x : Point => bilinear sourceTerms densityMatrix left right (x-point)*kernel point)
      (convolutionDerivative left right position point) position := by
  have shift : HasFDerivAt (fun x : Point => bilinear sourceTerms densityMatrix left right (x-point))
      (bilinearLinear left right (position-point)) position := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (source_bilinear_hasFDerivAt left right (position-point)).comp position
        ((hasFDerivAt_id position).sub_const point)
  convert shift.mul_const (kernel point) using 1 <;> try rfl

theorem convolutionDerivative_measurable (left right : MultiIndex) (position : Point) :
    AEStronglyMeasurable (convolutionDerivative left right position) volume := by
  exact (kernel_measurable.smul
    ((bilinearLinear_continuous left right).comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable

theorem convolutionDerivative_bound (left right : MultiIndex) (radius : ℝ) (position point : Point)
    (inside : ‖position‖ ≤ radius) :
    ‖convolutionDerivative left right position point‖ ≤ translatedDerivativeEnvelope left right radius point*kernel point := by
  rw [convolutionDerivative, norm_smul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonnegative point)]
  have bound := mul_le_mul_of_nonneg_left (translated_derivative_bound left right radius position point inside)
    (kernel_nonnegative point)
  simpa only [mul_comm] using bound

theorem densityConvolution_hasFDerivAt (left right : MultiIndex) (position : Point) :
    HasFDerivAt (densityConvolution left right)
      (∫ point : Point, convolutionDerivative left right position point) position := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball position 1)
    (bound := fun point => translatedDerivativeEnvelope left right (‖position‖+1) point*kernel point)
    (ball_mem_nhds position (by norm_num))
  · apply Filter.Eventually.of_forall
    intro x
    exact (((bilinear_contDiff sourceTerms densityMatrix left right 0).continuous.comp
      (continuous_const.sub continuous_id)).measurable.mul kernel_measurable).aestronglyMeasurable
  · exact convolution_integrable left right position
  · exact convolutionDerivative_measurable left right position
  · apply Filter.Eventually.of_forall
    intro point x inside
    have distanceBound : ‖x-position‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using inside
    have triangle := norm_sub_norm_le x position
    exact convolutionDerivative_bound left right _ x point (by linarith)
  · exact translated_derivative_kernel_integrable left right (‖position‖+1)
  · exact Filter.Eventually.of_forall (fun point x _ => integrand_hasFDerivAt left right x point)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
