import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology
open private bare_analytic from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

theorem actual_cutoff_zero_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (test:SchwartzMap ℝ ℂ):mellin (coPoissonMuntzScaleRemainder test) c.value=0:=by
  rw [coPoissonMuntzScaleRemainder_mellin_factorization test (by linarith[c.rightHalf]) c.belowOne,
    zero,zero_mul]

/-- The exact original Xi order is consumed on the full Muntz field, before any Pa projection. -/
theorem actual_cutoff_original_order_factor (c:BurnolCompletedMellinCoordinate)
    (test:SchwartzMap ℝ ℂ) (w:ℂ) (positive:0<w.re) (below:w.re<1) (apart:w≠c.value):
    mellin (coPoissonMuntzScaleRemainder test) w/(w-c.value)^(order c.value)=
      bare c.value w*coPoissonMuntzEvenSourceMellin test w:=by
  have notZero:w≠0:=ne_of_apply_ne Complex.re (by simpa only [zero_re] using positive.ne')
  have notOne:w≠1:=ne_of_apply_ne Complex.re (by simpa only [one_re] using below.ne)
  have source:=generatedRiemannZeta_zero_factorization ActualAnalyticOwner c.value w
    notZero notOne (Gammaℝ_ne_zero_of_re_pos positive)
  rw [generatedRiemannZeta_eq_mathlib] at source
  rw [coPoissonMuntzScaleRemainder_mellin_factorization test positive below,source]
  field_simp [pow_ne_zero (order c.value) (sub_ne_zero.mpr apart)]

theorem actual_cutoff_original_order_limit (c:BurnolCompletedMellinCoordinate)
    (test:SchwartzMap ℝ ℂ):
    Tendsto (fun w:ℂ=>mellin (coPoissonMuntzScaleRemainder test) w/(w-c.value)^(order c.value))
      (𝓝[≠]c.value) (𝓝 (bare c.value c.value*coPoissonMuntzEvenSourceMellin test c.value)):=by
  have positive:0<c.value.re:=by linarith[c.rightHalf]
  have sourceContinuous:ContinuousAt (fun w:ℂ=>bare c.value w*coPoissonMuntzEvenSourceMellin test w) c.value:=
    (bare_analytic c).continuousAt.mul
      (coPoissonMuntzEvenSourceMellin_differentiableAt test c.value positive).continuousAt
  have strip:∀ᶠw:ℂ in 𝓝 c.value,0<w.re ∧ w.re<1:=
    ((continuous_re.tendsto c.value).eventually (Ioi_mem_nhds positive)).and
      ((continuous_re.tendsto c.value).eventually (Iio_mem_nhds c.belowOne))
  apply (sourceContinuous.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [strip.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w inside apart
  exact (actual_cutoff_original_order_factor c test w inside.1 inside.2 apart).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
