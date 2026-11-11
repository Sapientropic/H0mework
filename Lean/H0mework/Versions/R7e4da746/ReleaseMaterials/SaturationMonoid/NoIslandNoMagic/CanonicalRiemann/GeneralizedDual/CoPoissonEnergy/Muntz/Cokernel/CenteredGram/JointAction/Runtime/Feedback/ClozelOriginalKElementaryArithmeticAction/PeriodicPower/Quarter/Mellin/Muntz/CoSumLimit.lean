import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CoSumLimit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology
open private pweight pweight_summable channel channel_bound forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

theorem actual_forward_pointwise_limit (sources:ℕ→ℝ→ℂ) (source:ℝ→ℂ) (B:ℝ)
    (growth:∀N x,‖sources N x‖≤B*|x|)
    (pointwise:∀x,Tendsto (fun N:ℕ=>sources N x) atTop (𝓝 (source x))) (x:ℝ):
    Tendsto (fun N:ℕ=>burnolInnerGapForward (sources N) x) atTop
      (𝓝 (burnolInnerGapForward source x)):=by
  simp only [forward_reindex]
  apply tendsto_tsum_of_dominated_convergence (pweight_summable.mul_left (B*|x|))
  · intro n
    exact (pointwise (x/(n+1:ℕ))).const_mul _
  · exact Eventually.of_forall (fun N n=>channel_bound (sources N) B (growth N) n x)

theorem actual_reciprocal_mean_limit (sources:ℕ→ℝ→ℂ) (source:ℝ→ℂ) (B:ℝ)
    (measurable:∀N,Measurable (sources N))
    (growth:∀N x,‖sources N x‖≤B*|x|)
    (outside:∀N x,(1/2:ℝ)< |x|→sources N x=0)
    (pointwise:∀x,Tendsto (fun N:ℕ=>sources N x) atTop (𝓝 (source x))):
    Tendsto (fun N:ℕ=>∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*sources N u) atTop
      (𝓝 (∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*source u)):=by
  let major:ℝ→ℝ:=(Ioc (0:ℝ) (1/2)).indicator (fun _=>B)
  have majorInt:Integrable major:=
    (integrableOn_const (C:=B) (s:=Ioc (0:ℝ) (1/2))
      (by exact measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  apply tendsto_integral_of_dominated_convergence major
  · intro N
    exact ((Complex.measurable_ofReal.comp measurable_id).inv.mul
      (measurable N)).aestronglyMeasurable.restrict
  · exact majorInt.integrableOn
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    by_cases inside:u≤1/2
    · dsimp only [major]
      rw [indicator_of_mem (show u∈Ioc (0:ℝ) (1/2) from ⟨hu,inside⟩),norm_mul,
        norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
      calc
        _≤u⁻¹*(B*u):=mul_le_mul_of_nonneg_left
          (by simpa only [abs_of_pos hu] using growth N u) (inv_nonneg.mpr hu.le)
        _=B:=by field_simp [hu.ne']
    · dsimp only [major]
      rw [indicator_of_notMem (show u∉Ioc (0:ℝ) (1/2) from fun hx=>inside hx.2),
        outside N u (by rw [abs_of_pos hu];exact lt_of_not_ge inside),mul_zero,norm_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
    exact (pointwise u).const_mul _

theorem actual_forward_image_pointwise_limit (sources:ℕ→ℝ→ℂ) (source:ℝ→ℂ) (B:ℝ)
    (measurable:∀N,Measurable (sources N))
    (growth:∀N x,‖sources N x‖≤B*|x|)
    (outside:∀N x,(1/2:ℝ)< |x|→sources N x=0)
    (pointwise:∀x,Tendsto (fun N:ℕ=>sources N x) atTop (𝓝 (source x))) (x:ℝ):
    Tendsto (fun N:ℕ=>burnolInnerGapForward (sources N) x-
      ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*sources N u) atTop
      (𝓝 (burnolInnerGapForward source x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*source u)):=
  (actual_forward_pointwise_limit sources source B growth pointwise x).sub
    (actual_reciprocal_mean_limit sources source B measurable growth outside pointwise)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CoSumLimit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
