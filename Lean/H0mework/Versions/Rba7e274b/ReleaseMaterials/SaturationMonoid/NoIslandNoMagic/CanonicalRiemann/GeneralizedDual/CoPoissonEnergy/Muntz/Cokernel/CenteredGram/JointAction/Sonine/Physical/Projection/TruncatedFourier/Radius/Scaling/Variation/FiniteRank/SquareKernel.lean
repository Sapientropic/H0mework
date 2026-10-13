import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Phase
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local notation "μ" => (volume.restrict (symmetricInterval 1) : Measure ℝ)
local instance finiteUnit : IsFiniteMeasure μ where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

theorem phase_norm (r x y : ℝ) : ‖phase r x y‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  have actual : (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ)^2 * (x : ℂ) * (y : ℂ)).re = 0 := by
    simp [Complex.mul_re,Complex.mul_im,← Complex.ofReal_pow]
  rw [actual,Real.exp_zero]

theorem raw_phase (r : ℝ) (f : BurnolUnitIntervalL2) (x : ℝ) :
    burnolRadiusRechartedTruncatedFourierRaw r f x =
      (r : ℂ) * ∫ y : ℝ, phase r x y * f y ∂μ := by
  unfold burnolRadiusRechartedTruncatedFourierRaw
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  rw [← integral_smul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold phase
  simp only [smul_eq_mul,LinearMap.smul_apply,innerₗ_apply_apply,Real.inner_apply]
  push_cast
  ring_nf

theorem phase_integrable (r x : ℝ) (f : BurnolUnitIntervalL2) :
    Integrable (fun y : ℝ => phase r x y * f y) μ := by
  apply (burnolUnitState_integrable f).norm.mono'
  · exact (by unfold phase;fun_prop : Continuous (phase r x)).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul,phase_norm,one_mul]

theorem square_kernel_phase (r x y : ℝ) (_positive : 0 < r) :
    (r : ℂ)^2 * (∫ z : ℝ, phase r x z * phase r z y ∂μ) = squareKernel r x y := by
  have kernel : ∀ z : ℝ, phase r x z * phase r z y =
      Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(r:ℂ)^2*(z:ℂ)*((x+y:ℝ):ℂ)) := by
    intro z
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [kernel]
  unfold symmetricInterval
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
  unfold squareKernel
  have changed := intervalIntegral.smul_integral_comp_mul_left (a := (-1:ℝ)) (b := (1:ℝ))
    (fun t : ℝ => Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(t:ℂ)*((x+y:ℝ):ℂ))) (r^2 : ℝ)
  simp only [real_smul,Complex.ofReal_pow,mul_neg_one,mul_one] at changed
  convert! changed using 1
  congr 2
  funext z
  congr 1
  push_cast
  ring

theorem square_raw (r : ℝ) (positive : 0 < r) (f : BurnolUnitIntervalL2) :
    (burnolRadiusRechartedTruncatedFourier positive
      (burnolRadiusRechartedTruncatedFourier positive f) : ℝ → ℂ) =ᵐ[μ]
      fun x => ∫ y : ℝ, squareKernel r x y * f y ∂μ := by
  filter_upwards [burnolRadiusRechartedTruncatedFourier_coe positive
    (burnolRadiusRechartedTruncatedFourier positive f)] with x outer
  rw [outer,raw_phase]
  have inner := burnolRadiusRechartedTruncatedFourier_coe positive f
  have substitution : (∫ z : ℝ, phase r x z *
      (burnolRadiusRechartedTruncatedFourier positive f) z ∂μ) =
      ∫ z : ℝ, phase r x z * ((r:ℂ)*∫ y : ℝ,phase r z y*f y ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [inner] with z hz
    rw [hz,raw_phase]
  rw [substitution]
  have integrable : Integrable (fun pair : ℝ×ℝ => phase r x pair.1 * phase r pair.1 pair.2 * f pair.2) ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1))) := by
    apply ((burnolUnitState_integrable f).norm.comp_snd (volume.restrict (symmetricInterval 1))).mono'
    · exact ((by unfold phase;fun_prop : Continuous (fun pair : ℝ×ℝ => phase r x pair.1 * phase r pair.1 pair.2))).aestronglyMeasurable.mul
        ((Lp.memLp f).aestronglyMeasurable.comp_snd)
    · filter_upwards with pair
      rw [norm_mul,norm_mul,phase_norm,phase_norm,one_mul,one_mul]
  calc
    _ = (r:ℂ)^2 * ∫ z : ℝ,∫ y : ℝ, phase r x z * phase r z y * f y ∂μ ∂μ := by
      simp only [← integral_const_mul]
      ring
    _ = (r:ℂ)^2 * ∫ y : ℝ,∫ z : ℝ, phase r x z * phase r z y * f y ∂μ ∂μ := by
      rw [integral_integral_swap integrable]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_mul_const]
      have source := square_kernel_phase r x y positive
      rw [← mul_assoc,source]

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
