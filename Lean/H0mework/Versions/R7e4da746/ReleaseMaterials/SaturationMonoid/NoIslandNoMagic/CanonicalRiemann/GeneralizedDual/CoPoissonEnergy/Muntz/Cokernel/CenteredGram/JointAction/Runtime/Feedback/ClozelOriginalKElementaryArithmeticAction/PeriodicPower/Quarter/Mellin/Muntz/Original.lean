import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Actual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ResonantMoment
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Original
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Actual OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ResonantMoment
open scoped Topology
open private channel forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private tate_channel tate_reciprocal_integral from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open private bare_analytic from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
local notation "owner"=>ActualAnalyticOwner
local notation "order"=>generatedRiemannXiZeroOrder owner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum owner

private theorem counted_native (c:BurnolCompletedMellinCoordinate) (h:ℝ) (x:ℝ) (positive:0<x):
    countedRaw c h x=countedImage (directRaw c h) x:=by
  have mean:reciprocalMean c h=∫u:ℝ in Ioi 0,directRaw c h u:=by
    rw [reciprocalMean,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.tateRaw,tate_reciprocal_integral]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun u hu=>(actual_direct_nonzero c h u (ne_of_gt hu)).symm)
  have channels (n:ℕ):channel (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.tateRaw c h) n x=
      (x:ℂ)⁻¹*directRaw c h ((n+1:ℕ)/x):=by
    have positiveIndex:(0:ℕ)<n+1:=Nat.succ_pos n
    have positiveArg:0<((n+1:ℕ):ℝ)/x:=div_pos (by positivity) positive
    have same:=tate_channel c h x positive.ne' (n+1) positiveIndex
    rw [abs_of_pos positive,←actual_direct_nonzero c h _ positiveArg.ne'] at same
    exact same
  rw [countedRaw,forward_reindex,mean,countedImage]
  simp_rw [channels]
  rw [tsum_mul_left]

theorem actual_native_counted_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (countedRaw c h) w=riemannZeta (1-w)*mellin (directRaw c h) (1-w):=by
  rw [←actual_counted_mellin c zero h nonnegative w positive below]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun x hx=>congrArg (fun value:ℂ=>(x:ℂ)^(w-1) • value) (counted_native c h x hx))

theorem actual_native_counted_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):mellin (countedRaw c h) (1-c.value)=0:=by
  rw [actual_native_counted_mellin c zero h nonnegative (1-c.value)
    (by simp only [sub_re,one_re];linarith[c.belowOne])
    (by simp only [sub_re,one_re];linarith[c.rightHalf]),
    show 1-(1-c.value)=c.value by ring,zero,zero_mul]

private theorem original_factor (c:BurnolCompletedMellinCoordinate) (z:ℂ)
    (positive:0<z.re) (below:z.re<1):
    riemannZeta z=(z-c.value)^(order c.value)*bare c.value z:=by
  have source:=generatedRiemannZeta_zero_factorization owner c.value z
    (ne_of_apply_ne Complex.re (by simpa only [zero_re] using positive.ne'))
    (ne_of_apply_ne Complex.re (by simpa only [one_re] using below.ne))
    (Gammaℝ_ne_zero_of_re_pos positive)
  simpa only [generatedRiemannZeta_eq_mathlib,smul_eq_mul] using source

theorem actual_native_counted_order_factor (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (z:ℂ) (positive:0<z.re) (below:z.re<1) (apart:z≠c.value):
    mellin (countedRaw c h) (1-z)/(z-c.value)^(order c.value)=
      bare c.value z*mellin (directRaw c h) z:=by
  rw [actual_native_counted_mellin c zero h nonnegative (1-z)
    (by simp only [sub_re,one_re];linarith)
    (by simp only [sub_re,one_re];linarith),show 1-(1-z)=z by ring,
    original_factor c z positive below]
  field_simp [pow_ne_zero (order c.value) (sub_ne_zero.mpr apart)]

theorem actual_native_counted_order_limit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):
    Tendsto (fun z:ℂ=>mellin (countedRaw c h) (1-z)/(z-c.value)^(order c.value))
      (𝓝[≠]c.value) (𝓝 (bare c.value c.value*mellin (directRaw c h) c.value)):=by
  have continuous:ContinuousAt (fun z:ℂ=>bare c.value z*mellin (directRaw c h) z) c.value:=
    (bare_analytic c).continuousAt.mul
      (actual_direct_mellin_continuous c zero h nonnegative c.value (by linarith[c.rightHalf]))
  apply (continuous.tendsto.mono_left nhdsWithin_le_nhds).congr'
  have strip:∀ᶠz:ℂ in 𝓝 c.value,0<z.re ∧ z.re<1:=
    ((continuous_re.tendsto c.value).eventually (Ioi_mem_nhds (by linarith[c.rightHalf]))).and
      ((continuous_re.tendsto c.value).eventually (Iio_mem_nhds c.belowOne))
  filter_upwards [strip.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z inside apart
  exact (actual_native_counted_order_factor c zero h nonnegative z inside.1 inside.2 apart).symm

private def conjugateCoordinate (c:BurnolCompletedMellinCoordinate):BurnolCompletedMellinCoordinate:=
  ⟨star c.value,by simpa only [star_def,conj_re] using c.rightHalf,
    by simpa only [star_def,conj_re] using c.belowOne⟩

/-- The resonant image uses the conjugate occurrence, while its multiplicity remains the original m. -/
theorem actual_native_forward_order_factor (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (z:ℂ) (positive:0<z.re) (below:z.re<1) (apart:z≠star c.value):
    mellin (directField c h) (1-z)/(z-star c.value)^(order c.value)=
      bare (star c.value) z*mellin (directRaw c h) (1-z):=by
  have source:=original_factor (conjugateCoordinate c) z positive below
  change riemannZeta z=(z-star c.value)^(order (star c.value))*bare (star c.value) z at source
  rw [OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c] at source
  rw [actual_forward_mellin c zero h nonnegative (1-z)
    (by simp only [sub_re,one_re];linarith)
    (by simp only [sub_re,one_re];linarith),show 1-(1-z)=z by ring,source]
  field_simp [pow_ne_zero (order c.value) (sub_ne_zero.mpr apart)]

theorem actual_native_forward_resonant_order_limit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):
    Tendsto (fun z:ℂ=>mellin (directField c h) (1-z)/(z-star c.value)^(order c.value))
      (𝓝[≠](star c.value))
      (𝓝 (bare (star c.value) (star c.value)*
        (-(h:ℂ)*Complex.exp ((star c.value-1/2)*(h:ℂ))*
          OriginalRieszFinitePairing.CoPoisson.Ward.ForcingPrimitive.leadingCoefficient c))):=by
  have below:(star c.value).re<1:=by simpa only [star_def,conj_re] using c.belowOne
  have above:(1/2:ℝ)<(star c.value).re:=by simpa only [star_def,conj_re] using c.rightHalf
  have sourceContinuous:ContinuousAt (fun z:ℂ=>mellin (directRaw c h) (1-z)) (star c.value):=
    (actual_direct_mellin_continuous c zero h nonnegative (1-star c.value)
      (by simp only [sub_re,one_re];linarith)).comp (continuousAt_const.sub continuousAt_id)
  have bareContinuous:ContinuousAt (bare (star c.value)) (star c.value):=
    (bare_analytic (conjugateCoordinate c)).continuousAt
  have limit:Tendsto (fun z:ℂ=>bare (star c.value) z*mellin (directRaw c h) (1-z))
      (𝓝[≠](star c.value))
      (𝓝 (bare (star c.value) (star c.value)*mellin (directRaw c h) (1-star c.value))):=
    (bareContinuous.mul sourceContinuous).tendsto.mono_left nhdsWithin_le_nhds
  rw [(actual_difference_resonant_moment c zero h nonnegative).2] at limit
  apply limit.congr'
  have strip:∀ᶠz:ℂ in 𝓝 (star c.value),0<z.re ∧ z.re<1:=
    ((continuous_re.tendsto (star c.value)).eventually (Ioi_mem_nhds (by linarith))).and
      ((continuous_re.tendsto (star c.value)).eventually (Iio_mem_nhds below))
  filter_upwards [strip.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z inside apart
  exact (actual_native_forward_order_factor c zero h nonnegative z inside.1 inside.2 apart).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Original
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
