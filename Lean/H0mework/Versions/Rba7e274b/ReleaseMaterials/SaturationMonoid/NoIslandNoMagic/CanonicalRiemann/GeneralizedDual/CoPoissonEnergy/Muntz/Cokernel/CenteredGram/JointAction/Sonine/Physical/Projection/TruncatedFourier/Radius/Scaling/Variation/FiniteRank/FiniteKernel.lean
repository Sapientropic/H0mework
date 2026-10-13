import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.SquareKernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local notation "μ" => (volume.restrict (symmetricInterval 1) : Measure ℝ)
local instance finiteKernelUnit : IsFiniteMeasure μ where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

theorem square_kernel_norm (r x y : ℝ) : ‖squareKernel r x y‖ ≤ 2*r^2 := by
  unfold squareKernel
  have actual : ∀ t : ℝ, ‖Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(t:ℂ)*((x+y:ℝ):ℂ))‖≤1 := by
    intro t
    rw [Complex.norm_exp]
    have real : (-2*(Real.pi:ℂ)*Complex.I*(t:ℂ)*((x+y:ℝ):ℂ)).re=0 := by simp [Complex.mul_re,Complex.mul_im]
    rw [real,Real.exp_zero]
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(r^2)) (b := r^2) (C := 1) (fun t _ => actual t)
  simpa only [one_mul,Real.norm_eq_abs,show |r^2-(-(r^2))|=2*r^2 by rw [sub_neg_eq_add,abs_of_nonneg (by positivity)];ring] using bound

theorem square_kernel_integrable (r x : ℝ) (f : BurnolUnitIntervalL2) :
    Integrable (fun y : ℝ => squareKernel r x y*f y) μ := by
  apply ((burnolUnitState_integrable f).norm.const_mul (2*r^2)).mono'
  · have regular : Continuous (squareKernel r x) := by
      unfold squareKernel
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · fun_prop
      · fun_prop
    exact regular.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (square_kernel_norm r x y) (norm_nonneg _)

-- Exact finite change in the real original Fourier square, retaining both parity channels.
theorem square_finite_raw (q r : ℝ) (qPositive : 0<q) (rPositive : 0<r) (f : BurnolUnitIntervalL2) :
    (((burnolRadiusRechartedTruncatedFourier rPositive (burnolRadiusRechartedTruncatedFourier rPositive f) -
      burnolRadiusRechartedTruncatedFourier qPositive (burnolRadiusRechartedTruncatedFourier qPositive f) : BurnolUnitIntervalL2) : ℝ→ℂ)) =ᵐ[μ]
      fun x => ∫ y : ℝ, (∫ t : ℝ in q..r,
        (t:ℂ)*(cosineRaw t x*cosineRaw t y-sineRaw t x*sineRaw t y)) * f y ∂μ := by
  filter_upwards [Lp.coeFn_sub
      (burnolRadiusRechartedTruncatedFourier rPositive (burnolRadiusRechartedTruncatedFourier rPositive f))
      (burnolRadiusRechartedTruncatedFourier qPositive (burnolRadiusRechartedTruncatedFourier qPositive f)),
    square_raw r rPositive f,square_raw q qPositive f] with x difference rRead qRead
  rw [difference]
  simp only [Pi.sub_apply]
  rw [rRead,qRead,← integral_sub (square_kernel_integrable r x f) (square_kernel_integrable q x f)]
  apply integral_congr_ae
  filter_upwards with y
  rw [← sub_mul,square_kernel_finite]

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
