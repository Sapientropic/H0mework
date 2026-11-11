import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Mean

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Mean
open scoped Topology ENNReal
open private actual_fourier_linear_bound frequency_nonnegative from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
local notation "q"=>(1/4:ℝ)
local notation "leading"=>ForcingPrimitive.leadingCoefficient
local notation "μplus"=>volume.restrict (Ioi (0:ℝ))

def outerPower (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  if q < |x| then ((|x|:ℝ):ℂ)^(star c.value-1) else 0

def raw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  regularCompactRaw c x+dualFourierRaw c x-leading c*outerPower c x

theorem actual_even (c:BurnolCompletedMellinCoordinate) (x:ℝ):raw c (-x)=raw c x:=by
  rw [raw,raw,actual_regular_even,actual_dual_fourier_even]
  simp only [outerPower,abs_neg]

theorem actual_measurable (c:BurnolCompletedMellinCoordinate):Measurable (raw c):=by
  have fourier:Measurable (dualFourierRaw c):=
    (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne)).measurable
  have power:Measurable (outerPower c):=by
    apply Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable) _ measurable_const
    fun_prop
  exact ((actual_regular_measurable c).add fourier).sub (measurable_const.mul power)

/-- The genuine global joint field has this regular-origin and complete outer-tail source. -/
theorem actual_source (c:BurnolCompletedMellinCoordinate):
    (jointSource c:ℝ→ℂ)=ᵐ[volume]raw c:=by
  filter_upwards [actual_joint_homogeneous_raw c,volume.ae_ne (0:ℝ),volume.ae_ne q,volume.ae_ne (-q)]
    with x source nonzero notQuarter notMinus
  rw [source,raw]
  have positive:0 < |x|:=abs_pos.mpr nonzero
  have notBoundary:|x|≠q:=by
    intro same
    by_cases nonnegative:0≤x
    · rw [abs_of_nonneg nonnegative] at same
      exact notQuarter same
    · rw [abs_of_neg (lt_of_not_ge nonnegative)] at same
      exact notMinus (by linarith)
  by_cases inside:|x|<q
  · have member:x∈symmetricInterval q:=abs_le.mp inside.le
    have openMember:x∈Ioo (-q) q:=abs_lt.mp inside
    have periodic:OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c x=
        OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c |x|:=by
      by_cases nonnegative:0≤x
      · rw [abs_of_nonneg nonnegative]
      · rw [abs_of_neg (lt_of_not_ge nonnegative),OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action.actual_periodic_even]
    rw [quarterRaw,indicator_of_mem member,periodic,actual_periodic_split c |x| positive,
      regularCompactRaw,indicator_of_mem openMember,regularLocal,min_eq_right inside.le,
      outerPower,if_neg (not_lt.mpr inside.le)]
    ring
  · have outside:q < |x|:=lt_of_le_of_ne (le_of_not_gt inside) notBoundary.symm
    rw [quarterRaw,indicator_of_notMem (show x∉symmetricInterval q from
      fun member=>not_lt.mpr (abs_le.mpr member) outside),zero_add,
      actual_regular_outer_zero c x outside.le,zero_add,outerPower,if_pos outside]

private theorem raw_identity (c:BurnolCompletedMellinCoordinate):
    raw c=ᵐ[volume]jointSourceRaw c:=
  (actual_source c).symm.trans (actual_joint_source_raw c)

theorem actual_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):raw c 0=0:=by
  have fourier:dualFourierRaw c 0=0:=by
    apply norm_eq_zero.mp
    have bound:=actual_fourier_linear_bound c 0
    change ‖dualFourierRaw c 0‖≤_ at bound
    simp only [abs_zero,mul_zero] at bound
    exact le_antisymm bound (norm_nonneg _)
  rw [raw,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward.actual_regular_origin c zero,fourier,
    outerPower,abs_zero,if_neg (by norm_num),mul_zero]
  ring

private theorem outer_linear_bound (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    ‖outerPower c x‖≤(4*q^(c.value.re-1))*|x|:=by
  by_cases outside:q < |x|
  · have positive:0 < |x|:=lt_trans (by norm_num) outside
    rw [outerPower,if_pos outside,Complex.norm_cpow_eq_rpow_re_of_pos positive]
    have power:|x|^(c.value.re-1)≤q^(c.value.re-1):=
      Real.rpow_le_rpow_of_nonpos (by norm_num) outside.le (by linarith [c.belowOne])
    have exponent:(star c.value-1).re=c.value.re-1:=by simp only [sub_re,one_re,star_def,conj_re]
    rw [exponent]
    have nonnegative:0≤q^(c.value.re-1):=Real.rpow_nonneg (by norm_num) _
    nlinarith
  · rw [outerPower,if_neg outside,norm_zero]
    positivity

theorem actual_global_growth (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃B:ℝ,0≤B∧∀x:ℝ,‖raw c x‖≤B*|x|:=by
  obtain ⟨L,nonnegative,bound⟩:=actual_regular_global_growth c zero
  refine ⟨L+OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter.frequencyBound c+
    ‖leading c‖*(4*q^(c.value.re-1)),by
      have frequency:=frequency_nonnegative c
      positivity,?_⟩
  intro x
  calc
    _≤‖regularCompactRaw c x‖+‖dualFourierRaw c x‖+‖leading c*outerPower c x‖:=by
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤L*|x|+OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter.frequencyBound c*|x|+
        ‖leading c‖*((4*q^(c.value.re-1))*|x|):=by
      rw [norm_mul]
      gcongr
      · exact bound x
      · exact actual_fourier_linear_bound c x
      · exact outer_linear_bound c x
    _=_:=by ring

theorem actual_reciprocal_domain (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*raw c x) volume:=by
  let g:ℝ→ℂ:=fun x=>(x:ℂ)⁻¹*raw c x
  have positive:IntegrableOn g (Ioi 0):=by
    apply (actual_joint_reciprocal_integrable c zero).congr
    filter_upwards [ae_restrict_of_ae (raw_identity c)] with x source
    exact congrArg ((x:ℂ)⁻¹*·) source.symm
  have reflected:IntegrableOn (fun x:ℝ=>g (-x)) (Iio (0:ℝ)):=by
    have source:=((MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).2 positive)
    have set:Neg.neg ⁻¹' (Ioi (0:ℝ))=Iio 0:=by ext x;simp only [mem_preimage,mem_Ioi,neg_pos,mem_Iio]
    simpa only [Function.comp_def,set] using source
  have negative:IntegrableOn g (Iio 0):=by
    apply reflected.neg.congr
    filter_upwards with x
    dsimp only [g,Pi.neg_apply]
    rw [Complex.ofReal_neg,inv_neg,neg_mul,actual_even,neg_neg]
  have combined:IntegrableOn g ({(0:ℝ)}ᶜ):=by
    rw [←Iio_union_Ioi]
    exact negative.union positive
  simpa only [IntegrableOn,restrict_compl_singleton] using combined

theorem actual_reciprocal_mean (c:BurnolCompletedMellinCoordinate):
    (∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*raw c x)=jointReciprocalMean c:=by
  unfold jointReciprocalMean
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (raw_identity c)] with x source
  rw [source]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
