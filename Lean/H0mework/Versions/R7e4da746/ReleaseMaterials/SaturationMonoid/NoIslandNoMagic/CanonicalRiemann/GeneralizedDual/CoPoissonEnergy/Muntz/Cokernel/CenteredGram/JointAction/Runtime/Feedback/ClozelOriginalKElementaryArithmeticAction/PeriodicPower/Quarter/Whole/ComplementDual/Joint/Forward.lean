import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Homogeneous
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Forward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology
open private cutoffSet cutoff cutoff_measurableSet cutoff_measurable cutoff_norm cutoff_zero cutoff_even
  cutoff_tendsto forward_test_integrable forward_integral_limit from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private half_integral_even from
  H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.FaithfulForward

private theorem raw_cubic_forward (raw:ℝ→ℂ) (measurable:Measurable raw) (atZero:raw 0=0)
    (even:∀x,raw (-x)=raw x) (weighted:Integrable (fun x:ℝ=>‖raw x‖/|x|^3))
    (reciprocal:IntegrableOn (fun x:ℝ=>(x:ℂ)⁻¹*raw x) (Ioi 0)) (test:SchwartzMap ℝ ℂ)
    (paired:Integrable (fun x:ℝ=>raw x*coPoissonMuntzScaleRemainder test |x|)):
    (1/2:ℂ)*(∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x|)=
      (∫x:ℝ,test x*burnolInnerGapForward raw x)-
        (∫x:ℝ,test x)*(∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u):=by
  have thetaRead:(∫x:ℝ,test x*burnolInnerGapForward raw x)=
      ∫u:ℝ in Ioi 0,raw u*coPoissonMuntzThetaNonzero test u:=by
    have reindex (x:ℝ):burnolInnerGapForward raw x=
        ∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*raw (x/(n+1:ℕ)):=
      (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
        (fun n:ℕ+=>((n:ℕ):ℂ)⁻¹*raw (x/(n:ℕ)))).symm
    simp_rw [reindex]
    simpa only [FourierTransform.fourier_fourierInv_eq] using
      MobiusSourceFourierPairing.integral_forward_eq_positiveTheta raw measurable atZero even weighted
        (FourierTransform.fourierInv test)
  have thetaDomain:IntegrableOn (fun u:ℝ=>raw u*coPoissonMuntzThetaNonzero test u) (Ioi 0):=by
    simpa only [FourierTransform.fourier_fourierInv_eq] using
      MobiusSourceFourierPairing.positiveTheta_integrable raw measurable atZero even weighted
        (FourierTransform.fourierInv test)
  rw [half_integral_even _ paired (fun x=>by rw [even,abs_neg])]
  calc
    _=∫u:ℝ in Ioi 0,raw u*coPoissonMuntzThetaNonzero test u-
        (∫x:ℝ,test x)*((u:ℂ)⁻¹*raw u):=by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u positive
      dsimp only
      rw [abs_of_pos positive,coPoissonMuntzScaleRemainder_eq test positive]
      simp only [Complex.real_smul,Complex.ofReal_inv]
      ring
    _=_:=by rw [integral_sub thetaDomain (reciprocal.const_mul _),integral_const_mul,←thetaRead]

private theorem cutoff_cubic_integrable (raw:ℝ→ℂ) (measurable:Measurable raw)
    (reciprocal:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*raw x)) (N:ℕ):
    Integrable (fun x:ℝ=>‖cutoff raw N x‖/|x|^3):=by
  have weighted:Integrable (fun x:ℝ=>‖raw x‖/|x|):=by
    simpa only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,div_eq_mul_inv,mul_comm]
      using reciprocal.norm
  apply (weighted.mul_const ((N+1:ℝ)^2)).mono'
    (((cutoff_measurable raw measurable N).norm).div
      (continuous_abs.measurable.pow_const 3)).aestronglyMeasurable
  filter_upwards with x
  dsimp only [Pi.div_apply]
  rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg x) 3))]
  by_cases active:x∈cutoffSet N
  · have positive:0 < |x|:=(inv_pos.mpr (by positivity:(0:ℝ)<N+1)).trans_le active
    have inverse:|x|⁻¹≤(N+1:ℝ):=by
      have source:=(inv_le_inv₀ positive (inv_pos.mpr (by positivity:(0:ℝ)<N+1))).mpr active
      simpa only [inv_inv] using source
    rw [cutoff,indicator_of_mem active]
    calc
      _=(‖raw x‖/|x|)*(|x|⁻¹)^2:=by field_simp [positive.ne']
      _≤_:=mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr positive.le) inverse 2) (by positivity)
  · rw [cutoff,indicator_of_notMem active,norm_zero,zero_div]
    positivity

private theorem cutoff_reciprocal_integrable (raw:ℝ→ℂ)
    (domain:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*raw x)) (N:ℕ):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*cutoff raw N x):=by
  apply (domain.indicator (cutoff_measurableSet N)).congr
  filter_upwards with x
  rw [cutoff]
  by_cases active:x∈cutoffSet N
  · rw [indicator_of_mem active,indicator_of_mem active]
  · rw [indicator_of_notMem active,indicator_of_notMem active,mul_zero]

private theorem cutoff_paired_integrable (raw:ℝ→ℂ) (test:SchwartzMap ℝ ℂ)
    (domain:Integrable (fun x:ℝ=>raw x*coPoissonMuntzScaleRemainder test |x|)) (N:ℕ):
    Integrable (fun x:ℝ=>cutoff raw N x*coPoissonMuntzScaleRemainder test |x|):=by
  apply (domain.indicator (cutoff_measurableSet N)).congr
  filter_upwards with x
  rw [cutoff]
  by_cases active:x∈cutoffSet N
  · rw [indicator_of_mem active,indicator_of_mem active]
  · rw [indicator_of_notMem active,indicator_of_notMem active,zero_mul]

/-- Linear origin control and the actual reciprocal/comb domains suffice; the raw source need not be L2. -/
theorem actual_regular_remainder_forward (raw:ℝ→ℂ) (measurable:Measurable raw) (atZero:raw 0=0)
    (even:∀x,raw (-x)=raw x) (B:ℝ) (growth:∀x,‖raw x‖≤B*|x|)
    (reciprocal:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*raw x)) (test:SchwartzMap ℝ ℂ)
    (paired:Integrable (fun x:ℝ=>raw x*coPoissonMuntzScaleRemainder test |x|)):
    (1/2:ℂ)*(∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x|)=
      ∫x:ℝ,test x*(burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u):=by
  have kernel: AEStronglyMeasurable (fun x:ℝ=>coPoissonMuntzScaleRemainder test |x|):=
    ((Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)).aestronglyMeasurable
  have finite (N:ℕ):
      (1/2:ℂ)*(∫x:ℝ,cutoff raw N x*coPoissonMuntzScaleRemainder test |x|)=
        (∫x:ℝ,test x*burnolInnerGapForward (cutoff raw N) x)-
          (∫x:ℝ,test x)*(∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*cutoff raw N u):=
    raw_cubic_forward _ (cutoff_measurable raw measurable N) (cutoff_zero raw N)
      (cutoff_even raw even N) (cutoff_cubic_integrable raw measurable reciprocal N)
      (cutoff_reciprocal_integrable raw reciprocal N).integrableOn test (cutoff_paired_integrable raw test paired N)
  have sourceLimit:Tendsto (fun N:ℕ=>∫x:ℝ,cutoff raw N x*coPoissonMuntzScaleRemainder test |x|)
      atTop (𝓝 (∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x|)):=by
    apply tendsto_integral_of_dominated_convergence (fun x:ℝ=>‖raw x*coPoissonMuntzScaleRemainder test |x|‖)
    · intro N
      exact (cutoff_measurable raw measurable N).aestronglyMeasurable.mul kernel
    · exact paired.norm
    · intro N
      filter_upwards with x
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (cutoff_norm raw N x) (norm_nonneg _)
    · exact Eventually.of_forall (fun x=>(cutoff_tendsto raw atZero x).mul_const _)
  have meanLimit:Tendsto (fun N:ℕ=>∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*cutoff raw N x)
      atTop (𝓝 (∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*raw x)):=by
    apply tendsto_integral_of_dominated_convergence (fun x:ℝ=>‖(x:ℂ)⁻¹*raw x‖)
    · intro N
      exact (cutoff_reciprocal_integrable raw reciprocal N).aestronglyMeasurable.restrict
    · exact reciprocal.norm.integrableOn
    · intro N
      filter_upwards with x
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (cutoff_norm raw N x) (norm_nonneg _)
    · exact Eventually.of_forall (fun x=>(cutoff_tendsto raw atZero x).const_mul _)
  have targetLimit:=(forward_integral_limit raw measurable atZero B growth test).sub
    (meanLimit.const_mul (∫x:ℝ,test x))
  have source:=tendsto_nhds_unique (sourceLimit.const_mul (1/2:ℂ))
    (targetLimit.congr' (Eventually.of_forall (fun N=>(finite N).symm)))
  rw [source]
  simp only [mul_sub]
  rw [integral_sub (forward_test_integrable raw measurable B growth test)
    (test.integrable.mul_const _),integral_mul_const]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Forward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
