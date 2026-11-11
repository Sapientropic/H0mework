import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Price
open Complex ComplexConjugate Filter FourierTransform MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology InnerProductSpace ENNReal
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem star_domain (raw:ℝ→ℂ) (domain:Integrable raw μq):
    Integrable (fun x:ℝ=>star (raw x)) μq:=
  (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp domain

private theorem continuous_pair_domain (raw test:ℝ→ℂ) (domain:Integrable raw μq)
    (regular:Continuous test):Integrable (fun x:ℝ=>star (raw x)*test x) μq:=by
  obtain ⟨B,bound⟩:=isCompact_Icc.exists_bound_of_continuousOn regular.continuousOn
  apply (star_domain raw domain).mul_bdd regular.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact bound x inside

private theorem inverse_fourier_read (state:Hq) (even:reflectRestricted q state=state) (x:ℝ):
    VectorFourier.fourierIntegral 𝐞 μq (-(innerₗ ℝ).flip) (state:ℝ→ℂ) x=
      Constructor.fourierRaw state x:=by
  have evenAE:∀ᵐ y:ℝ ∂μq,state (-y)=state y:=by
    filter_upwards [Lp.coeFn_compMeasurePreserving state (negMeasurePreserving_restrict q)] with y reflected
    change reflectRestricted q state y=state (-y) at reflected
    rw [even] at reflected
    exact reflected.symm
  have moved:=(negMeasurePreserving_restrict q).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding
    (fun y:ℝ=>𝐞 (-(innerₗ ℝ) y x) • state y)
  calc
    _=∫y:ℝ,𝐞 (-(innerₗ ℝ) (-y) x) • state (-y) ∂μq:=by
      unfold VectorFourier.fourierIntegral
      apply integral_congr_ae
      filter_upwards [evenAE] with y actual
      rw [actual]
      simp only [LinearMap.neg_apply,LinearMap.flip_apply,innerₗ_apply_apply,Real.inner_apply,neg_mul,neg_neg]
      rw [mul_comm x y]
    _=_:=moved

theorem actual_mixed_fourier_pair (raw:ℝ→ℂ) (domain:Integrable raw μq)
    (state:M) (even:reflectRestricted q (state:Hq)=(state:Hq)):
    inner ℂ (smooth raw domain) state=
      ∫x:ℝ,star (raw x)*Constructor.fourierRaw (state:Hq) x ∂μq:=by
  have swapped:=VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (e:=𝐞) (μ:=μq) (ν:=μq) (L:=innerₗ ℝ) (innerSL ℂ)
    Real.continuous_fourierChar continuous_inner domain
    ((Lp.memLp (state:Hq)).integrable (by norm_num))
  have initial:inner ℂ (smooth raw domain) state=
      ∫x:ℝ,star (Constructor.fourierRaw raw x)*(state:Hq) x ∂μq:=by
    unfold smooth Constructor.zeroMean
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Constructor.compact_read (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain)] with x source
    rw [source]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    ring
  rw [initial]
  simp only [innerSL_apply_apply,RCLike.inner_apply,starRingEnd_apply] at swapped
  simp_rw [inverse_fourier_read (state:Hq) even] at swapped
  simpa only [Constructor.fourierRaw,mul_comm] using swapped

theorem actual_mixed_centered_pair (raw:ℝ→ℂ) (domain:Integrable raw μq)
    (mean:(∫x:ℝ,raw x ∂μq)=0) (state:M)
    (even:reflectRestricted q (state:Hq)=(state:Hq)):
    inner ℂ (smooth raw domain) state=
      ∫x:ℝ,star (raw x)*burnolMeanZeroFourierRaw state x ∂μq:=by
  rw [actual_mixed_fourier_pair raw domain state even]
  have direct:=continuous_pair_domain raw (Constructor.fourierRaw (state:Hq)) domain
    (burnolRadiusTruncatedFourierRaw_continuous (state:Hq))
  have constant:Integrable (fun x:ℝ=>star (raw x)*
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq))) μq:=
    (star_domain raw domain).mul_const _
  simp only [burnolMeanZeroFourierRaw,mul_sub]
  change Integrable (fun x:ℝ=>star (raw x)*burnolRadiusTruncatedFourierRaw q (state:Hq) x) μq at direct
  rw [Constructor.fourierRaw_state]
  rw [integral_sub direct constant,integral_mul_const]
  have meanStar:(∫x:ℝ,star (raw x) ∂μq)=0:=by
    rw [show (fun x:ℝ=>star (raw x))=(fun x:ℝ=>conj (raw x)) from rfl,integral_conj,mean,map_zero]
  rw [meanStar,zero_mul,sub_zero]

private theorem returned_even (state:M) (even:reflectRestricted q (state:Hq)=(state:Hq)):
    reflectRestricted q (S state:Hq)=(S state:Hq):=by
  have fixed:sourceMeanZeroReflection state=state:=Subtype.ext even
  have generated:=sourceMeanZeroFourier_reflect state
  rw [fixed] at generated
  exact (congrArg (fun a:M=>(a:Hq)) generated).symm

theorem actual_correction_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (below:w.re<1):
    inner ℂ (correction w below) (Constructor.zeroMean (forwardQuarter c zero))=
      ∫x:ℝ,star (seedRaw w x)*burnolMeanZeroFourierRaw (S (sourceInverse c zero)) x ∂μq:=by
  have equation:sourceInverse c zero-S (S (sourceInverse c zero))=Constructor.zeroMean (forwardQuarter c zero):=by
    change (burnolMeanZeroOneMinusSquare*burnolMeanZeroBlockInverse) (Constructor.zeroMean (forwardQuarter c zero))=_
    rw [burnolMeanZeroBlockInverse_right]
    rfl
  have even:=actual_inverse_reflection c zero
  have secondEven:=returned_even (sourceInverse c zero) even
  rw [←equation,inner_sub_right,
    ←meanZero_fourier_pairing_of_reflection (correction w below) (S (sourceInverse c zero)) secondEven,
    ←meanZero_fourier_pairing_of_reflection (S (correction w below)) (sourceInverse c zero) even,
    ←inner_sub_left,actual_correction_equation,
    meanZero_fourier_pairing_of_reflection (firstSource w below) (sourceInverse c zero) even]
  exact actual_mixed_centered_pair (seedRaw w) (actual_seed_integrable w below)
    (actual_seed_mean w below) (S (sourceInverse c zero)) secondEven

private theorem inverse_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (∫x:ℝ,inverseRaw c zero x ∂μq)=0:=by
  rw [←integral_congr_ae (actual_inverse_raw c zero)]
  have mean:=Constructor.mean_zero (sourceInverse c zero)
  rw [Constructor.mean_integral] at mean
  exact (mul_eq_zero.mp mean).resolve_left (by norm_num)

private theorem power_star (w:ℂ) (x:ℝ) (positive:0<x):
    star (powerRaw w x)=(x:ℂ)^(-w):=by
  have arg:(x:ℂ).arg≠Real.pi:=by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact ne_of_lt Real.pi_pos
  have generated:=(Complex.conj_cpow (x:ℂ) (-w) arg).symm
  simpa only [powerRaw,abs_of_pos positive,star_def,map_neg,Complex.conj_ofReal] using generated

private theorem power_inverse_half (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (below:w.re<1):
    (∫x:ℝ,star (powerRaw w x)*inverseRaw c zero x ∂μq)=
      2*(∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x):=by
  let product:ℝ→ℂ:=fun x=>star (powerRaw w x)*inverseRaw c zero |x|
  have domain:Integrable product μq:=continuous_pair_domain (powerRaw w) _
    (actual_power_integrable w below) ((actual_inverse_continuous c zero).comp continuous_abs)
  have even:∀x:ℝ,product (-x)=product x:=by
    intro x
    simp only [product,powerRaw,abs_neg]
  have whole:(∫x:ℝ,star (powerRaw w x)*inverseRaw c zero x ∂μq)=∫x:ℝ,product x ∂μq:=by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
    dsimp only [product]
    congr 1
    rcases le_total 0 x with nonnegative|nonpositive
    · rw [abs_of_nonneg nonnegative]
    · rw [abs_of_nonpos nonpositive,actual_inverse_raw_even c zero x inside]
  rw [whole,even_half_integral product domain even,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  dsimp only [product]
  rw [power_star w x inside.1,abs_of_pos inside.1]

theorem actual_seed_inverse_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (below:w.re<1):
    (∫x:ℝ,star (seedRaw w x)*inverseRaw c zero x ∂μq)=
      ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x:=by
  have powerDomain:=continuous_pair_domain (powerRaw w) _
    (actual_power_integrable w below) (actual_inverse_continuous c zero)
  have constantDomain:Integrable (fun x:ℝ=>star (rawMean (powerRaw w))*inverseRaw c zero x) μq:=
    ((actual_inverse_continuous c zero).integrableOn_Icc).const_mul _
  have split:(fun x:ℝ=>star (seedRaw w x)*inverseRaw c zero x)=
      fun x:ℝ=>(1/2:ℂ)*(star (powerRaw w x)*inverseRaw c zero x-
        star (rawMean (powerRaw w))*inverseRaw c zero x):=by
    funext x
    simp only [seedRaw,star_mul,star_sub,star_div₀,star_one,star_ofNat]
    ring
  rw [split,integral_const_mul,integral_sub powerDomain constantDomain,integral_const_mul,
    inverse_mean c zero,mul_zero,sub_zero,power_inverse_half c zero w below]
  ring

/-- The non-L² complementary test is generated by one genuine Fourier smoothing and the original BI. -/
theorem actual_dual_inverse_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (below:w.re<1):
    (∫x:ℝ,star (dualRaw w below x)*quarterBankRaw c x ∂μq)=
      ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x:=by
  let Qraw:ℝ→ℂ:=fun x=>quarterBankRaw c x-burnolQuarterMeanCoefficient (forwardQuarter c zero)
  have Qcontinuous:Continuous Qraw:=(actual_quarter_bank_continuous c zero).sub continuous_const
  have Qread:(Constructor.zeroMean (forwardQuarter c zero):ℝ→ℂ)=ᵐ[μq]Qraw:=by
    rw [Constructor.zeroMean_read]
    filter_upwards [Lp.coeFn_sub (forwardQuarter c zero)
      (burnolQuarterMeanCoefficient (forwardQuarter c zero) • intervalConstant q),
      Lp.coeFn_smul (burnolQuarterMeanCoefficient (forwardQuarter c zero)) (intervalConstant q),
      intervalConstant_coeFn q,actual_quarter_bank_raw c zero] with x subtracted scalar constant raw
    rw [subtracted,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one,raw]
  have originalCorrection:(∫x:ℝ,star (correctionRaw w below x)*Qraw x ∂μq)=
      inner ℂ (correction w below) (Constructor.zeroMean (forwardQuarter c zero)):=by
    change _=inner ℂ (correction w below:Hq) (Constructor.zeroMean (forwardQuarter c zero):Hq)
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actual_correction_raw w below,Qread] with x b Q
    rw [b,Q]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    ring
  have meanStar:(∫x:ℝ,star (dualRaw w below x) ∂μq)=0:=by
    rw [show (fun x:ℝ=>star (dualRaw w below x))=(fun x:ℝ=>conj (dualRaw w below x)) from rfl,
      integral_conj,actual_dual_mean,map_zero]
  have centered:(∫x:ℝ,star (dualRaw w below x)*quarterBankRaw c x ∂μq)=
      ∫x:ℝ,star (dualRaw w below x)*Qraw x ∂μq:=by
    dsimp only [Qraw]
    simp only [mul_sub]
    rw [integral_sub
      (continuous_pair_domain _ _ (actual_dual_integrable w below) (actual_quarter_bank_continuous c zero))
      ((star_domain _ (actual_dual_integrable w below)).mul_const _),integral_mul_const,meanStar,zero_mul,sub_zero]
  have seedSplit:(∫x:ℝ,star (seedRaw w x)*Qraw x ∂μq)=
      (∫x:ℝ,star (seedRaw w x)*inverseRaw c zero x ∂μq)-
        ∫x:ℝ,star (seedRaw w x)*burnolMeanZeroFourierRaw (S (sourceInverse c zero)) x ∂μq:=by
    rw [←integral_sub
      (continuous_pair_domain _ _ (actual_seed_integrable w below) (actual_inverse_continuous c zero))
      (continuous_pair_domain (seedRaw w) (burnolMeanZeroFourierRaw (S (sourceInverse c zero)))
        (actual_seed_integrable w below)
        ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const))]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [Qraw,inverseRaw]
    ring
  rw [centered]
  simp only [dualRaw,star_add,add_mul]
  rw [integral_add (continuous_pair_domain _ _ (actual_seed_integrable w below) Qcontinuous)
    (continuous_pair_domain _ _ (actual_correction_continuous w below).integrableOn_Icc Qcontinuous),
    originalCorrection,actual_correction_price c zero w below,seedSplit,sub_add_cancel,
    actual_seed_inverse_price c zero w below]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Price
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
