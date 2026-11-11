import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Limit

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Limit
open scoped Topology ENNReal InnerProductSpace
open private actual_fourier_linear_bound frequency_nonnegative from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open private original_fourier_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
local notation "q" => (1/4:ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μplus" => volume.restrict (Ioi (0:ℝ))
local notation "μtail" => volume.restrict (Ioi (1:ℝ))

private theorem inverse_tail_memLp:MemLp (fun x:ℝ=>(x:ℂ)⁻¹) 2 μtail:=by
  have measured:AEStronglyMeasurable (fun x:ℝ=>(x:ℂ)⁻¹) μtail:=by fun_prop
  apply (memLp_two_iff_integrable_sq_norm measured).mpr
  have power:Integrable (fun x:ℝ=>x^(-(2:ℝ))) μtail:=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  apply power.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x outside
  have positive:0<x:=lt_trans (by norm_num) outside
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  rw [Real.rpow_neg positive.le,Real.rpow_two,inv_pow]

private theorem reciprocal_L2_tail (value:BurnolL2):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*value x) μtail:=
  inverse_tail_memLp.integrable_mul ((Lp.memLp value).restrict _)

private theorem dual_fourier_split (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    dualFourierRaw c x=ForcingPrimitive.leadingCoefficient c*(x:ℂ)^(star c.value-1)-
      ForcingWhole.raw c x+Constructor.fourierRaw (correction c.value c.belowOne:Hq) x:=by
  have source:=congrFun (original_fourier_split c) x
  simp only [Pi.add_apply] at source
  have seed:=actual_seed_fourier_balance c x positive
  unfold dualFourierRaw
  linear_combination source+seed

private theorem reciprocal_origin_domain (c:BurnolCompletedMellinCoordinate):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x) (volume.restrict (Ioc (0:ℝ) 1)):=by
  have measurable:Measurable (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x):=
    Complex.continuous_ofReal.measurable.inv.mul
      (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne)).measurable
  apply (integrable_const (frequencyBound c)).mono' measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos inside.1]
  calc
    _≤x⁻¹*(frequencyBound c*x):=by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr inside.1.le)
      simpa only [dualFourierRaw,abs_of_pos inside.1] using actual_fourier_linear_bound c x
    _=frequencyBound c:=by field_simp [inside.1.ne']

private theorem reciprocal_tail_domain (c:BurnolCompletedMellinCoordinate):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x) μtail:=by
  have power:Integrable (fun x:ℝ=>(x:ℂ)^(star c.value-2)) μtail:=
    integrableOn_Ioi_cpow_of_lt (by
      change c.value.re-2 < -1
      linarith [c.belowOne]) (by norm_num)
  have forcing:=reciprocal_L2_tail (ForcingWhole.whole c)
  have forcingRaw:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*ForcingWhole.raw c x) μtail:=by
    apply forcing.congr
    filter_upwards [ae_restrict_of_ae (ForcingWhole.whole_read c)] with x source
    rw [source]
  have returned:=reciprocal_L2_tail (fourierL2 (E (correction c.value c.belowOne:Hq)))
  have returnedRaw:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*
      Constructor.fourierRaw (correction c.value c.belowOne:Hq) x) μtail:=by
    apply returned.congr
    filter_upwards [ae_restrict_of_ae (burnolRadiusFourierL2_zeroExtension_ae_eq_raw
      (correction c.value c.belowOne:Hq))] with x source
    change (fourierL2 (E (correction c.value c.belowOne:Hq)):ℝ→ℂ) x=
      Constructor.fourierRaw (correction c.value c.belowOne:Hq) x at source
    rw [source]
  apply (((power.const_mul (ForcingPrimitive.leadingCoefficient c)).sub forcingRaw).add returnedRaw).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x outside
  have positive:0<x:=lt_trans (by norm_num) outside
  rw [dual_fourier_split c x positive]
  have combined:(x:ℂ)⁻¹*(x:ℂ)^(star c.value-1)=(x:ℂ)^(star c.value-2):=by
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  dsimp only [Pi.add_apply,Pi.sub_apply]
  rw [mul_add,mul_sub,mul_left_comm _ (ForcingPrimitive.leadingCoefficient c),combined]

theorem actual_positive_reciprocal_integrable (c:BurnolCompletedMellinCoordinate):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x) μplus:=by
  have combined:IntegrableOn (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x)
      (Ioc (0:ℝ) 1∪Ioi 1):=IntegrableOn.union (reciprocal_origin_domain c) (reciprocal_tail_domain c)
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] at combined

theorem actual_dual_fourier_even (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    dualFourierRaw c (-x)=dualFourierRaw c x:=by
  rw [dualFourierRaw,Constructor.fourierRaw_integral,Constructor.fourierRaw_integral]
  have moved:=intervalIntegral.integral_comp_neg
    (f:=fun y:ℝ=>Constructor.phase x y*dualRaw c.value c.belowOne y) (a:=-q) (b:=q)
  calc
    _=∫y:ℝ in (-q)..q,Constructor.phase x (-y)*dualRaw c.value c.belowOne (-y):=by
      apply intervalIntegral.integral_congr
      intro y inside
      rw [uIcc_of_le (by norm_num : (-q:ℝ)≤q)] at inside
      dsimp only
      rw [actual_dual_even c.value c.belowOne y inside]
      simp only [Constructor.phase,neg_mul,mul_neg,neg_neg]
    _=_:=by simpa only [neg_neg] using moved

/-- The reciprocal source has its real global L1 domain; no full unweighted Fourier L2 is assumed. -/
theorem actual_reciprocal_integrable (c:BurnolCompletedMellinCoordinate):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*dualFourierRaw c x) volume:=by
  let g:ℝ→ℂ:=fun x=>(x:ℂ)⁻¹*dualFourierRaw c x
  have positive:IntegrableOn g (Ioi 0):=actual_positive_reciprocal_integrable c
  have reflected:IntegrableOn (fun x:ℝ=>g (-x)) (Iio (0:ℝ)):=by
    have source:=((MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).2 positive)
    have set:Neg.neg ⁻¹' (Ioi (0:ℝ))=Iio 0:=by ext x;simp only [mem_preimage,mem_Ioi,neg_pos,mem_Iio]
    simpa only [Function.comp_def,set] using source
  have negative:IntegrableOn g (Iio 0):=by
    apply reflected.neg.congr
    filter_upwards with x
    dsimp only [g,Pi.neg_apply]
    rw [Complex.ofReal_neg,inv_neg,neg_mul,actual_dual_fourier_even,neg_neg]
  have combined:IntegrableOn g ({(0:ℝ)}ᶜ):=by
    rw [←Iio_union_Ioi]
    exact negative.union positive
  simpa only [IntegrableOn,restrict_compl_singleton] using combined

/-- The complete counted Fourier source pays its second Unit by its genuine finite averages. -/
theorem actual_dual_reciprocal_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    dualReciprocalMean c=-(2*deriv (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation.poleFreeSource c) 1/(1-star c.value)):=by
  apply actual_counted_reciprocal_mean (dualFourierRaw c)
    (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne))
    (frequencyBound c) (frequency_nonnegative c)
    (fun u positive=>by simpa only [dualFourierRaw,abs_of_pos positive] using actual_fourier_linear_bound c u)
    (actual_positive_reciprocal_integrable c) (fourierL2 (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor.fullFloorValue c zero))
    (2*deriv (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation.poleFreeSource c) 1/(1-star c.value))
  filter_upwards [actual_L2_fourier_raw c zero] with y raw
  rw [raw]
  exact actual_complete_fourier_source c zero y

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
