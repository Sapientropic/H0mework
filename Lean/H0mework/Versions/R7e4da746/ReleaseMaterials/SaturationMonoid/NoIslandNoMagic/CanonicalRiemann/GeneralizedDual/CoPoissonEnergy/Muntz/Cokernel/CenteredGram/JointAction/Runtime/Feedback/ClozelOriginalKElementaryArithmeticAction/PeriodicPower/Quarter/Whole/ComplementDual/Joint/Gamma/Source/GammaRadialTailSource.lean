import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaRadialRawSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaRadialTail
open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.GammaRadialRaw OriginalGamma.Source.GammaSeedExterior
open OriginalGamma.Source.KGamma
noncomputable section
private theorem reciprocal_power_price (a : ℂ) (x t : ℝ)
    (xpos : 0<x) (tpos : 0<t) :
    (4:ℂ)^a*(x:ℂ)^(-a)*(((x/(4*t^2):ℝ):ℂ)*(((x/(4*t):ℝ):ℂ)^(a-1)))=
      (t:ℂ)^(-a-1) := by
  have xzero : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr xpos.ne'
  have tzero : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr tpos.ne'
  have fourtzero : ((4*t:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity : 4*t≠0)
  have xp : (x:ℂ)^a≠0 := cpow_ne_zero_iff.mpr (Or.inl xzero)
  have tp : (t:ℂ)^a≠0 := cpow_ne_zero_iff.mpr (Or.inl tzero)
  have fp : (4:ℂ)^a≠0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have denominator : ((4*t:ℝ):ℂ)^a=(4:ℂ)^a*(t:ℂ)^a := by
    rw [Complex.ofReal_mul,mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤4) tpos.le,
      Complex.ofReal_ofNat]
  have scaledPower : ((x/(4*t):ℝ):ℂ)^(a-1)=
      (x:ℂ)^a/((4:ℂ)^a*(t:ℂ)^a)/((x:ℂ)/(4*(t:ℂ))) := by
    rw [Complex.ofReal_div,cpow_sub a 1 (div_ne_zero xzero fourtzero),cpow_one,
      div_cpow_ofReal_nonneg xpos.le (by positivity : 0≤4*t),denominator]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [scaledPower,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,
    cpow_sub (-a) 1 tzero,cpow_one,cpow_neg,cpow_neg]
  field_simp [xp,tp,fp,xzero,tzero]

theorem actual_original_gamma_mellin_primitive_integrable (c : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0<x) :
    IntegrableOn (fun y : ℝ=>(y:ℂ)^(star c.value-1)*gammaSeedRaw y) (Ioo 0 x) := by
  have powerMeasured : Measurable (fun y : ℝ=>(y:ℂ)^(star c.value-1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro y nonzero
    exact (Complex.continuousAt_ofReal_cpow_const y _ (Or.inr nonzero)).continuousWithinAt
  have powerMem : MemLp (fun y : ℝ=>(y:ℂ)^(star c.value-1)) 2 (volume.restrict (Ioo 0 x)) := by
    apply (memLp_two_iff_integrable_sq_norm powerMeasured.aestronglyMeasurable).mpr
    have exponent : -1<(2*(c.value.re-1):ℝ) := by linarith [c.rightHalf]
    have native := (intervalIntegral.intervalIntegrable_cpow'
      (r:=((2*(c.value.re-1):ℝ):ℂ)) (by simpa using exponent) (a:=0) (b:=x)).norm
    have actual : IntegrableOn (fun y : ℝ=>‖(y:ℂ)^((2*(c.value.re-1):ℝ):ℂ)‖) (Icc 0 x) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le positive.le).mp native
    apply (actual.mono_set Ioo_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y inside
    simp only [Complex.norm_cpow_eq_rpow_re_of_pos inside.1,sub_re,star_def,conj_re,one_re,
      Complex.ofReal_re]
    rw [show 2*(c.value.re-1)=(c.value.re-1)*2 by ring,Real.rpow_mul inside.1.le,Real.rpow_two]
  have seedMem : MemLp gammaSeedRaw 2 (volume.restrict (Ioo 0 x)) :=
    ((Lp.memLp actualGammaSeed).ae_eq actual_gamma_seed_whole_raw).mono_measure Measure.restrict_le_self
  exact memLp_one_iff_integrable.mp (seedMem.mul' powerMem)

end
end OriginalGamma.Source.GammaRadialTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
