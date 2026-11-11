import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.MellinValue
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.FinitePart
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ResonantMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.MellinValue
open scoped Topology InnerProductSpace
open private origin_bound log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private companion_whole_read companion_whole_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open private divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet
local notation "owner"=>ActualAnalyticOwner
local notation "order"=>generatedRiemannXiZeroOrder owner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum owner
local notation "q"=>(1/4:ℝ)

private theorem companion_mellin_continuous (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (strip : -1<w.re) : ContinuousAt (mellin (companionWholeRaw c)) w := by
  obtain ⟨B,_,growth⟩:=companion_whole_bound c zero
  have outside:∀x:ℝ,q < |x| → companionWholeRaw c x=0 := by
    intro x outside
    exact indicator_of_notMem (s:=symmetricInterval q)
      (fun inside=>not_le_of_gt outside (abs_le.mpr inside)) _
  have top:companionWholeRaw c=O[atTop](fun x:ℝ=>x^(-(w.re+1))) := by
    simpa only [logSource_zero] using log_top_bound (companionWholeRaw c) q outside 0 (w.re+1)
  have origin:companionWholeRaw c=O[𝓝[>] 0](fun x:ℝ=>x^(-(-1:ℝ))) := by
    simpa only [neg_neg] using origin_bound _ B growth
  have localSource:=(((Lp.memLp (companion c)).ae_eq (companion_whole_read c)).locallyIntegrable
    (by norm_num)).locallyIntegrableOn (Ioi (0:ℝ))
  exact (mellin_differentiableAt_of_isBigO_rpow localSource top (by linarith) origin strip).continuousAt

private theorem original_order_positive (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    0<order c.value :=
  generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero)

private theorem original_reverse_factor (c : BurnolCompletedMellinCoordinate) (w : ℂ)
    (positive : 0<w.re) (below : w.re<1) :
    riemannZeta (1-w)=(-(w-star c.value))^(order c.value)*bare (1-star c.value) (1-w) := by
  have positiveDual:0<(1-w).re := by simp only [sub_re,one_re];linarith
  have belowDual:(1-w).re<1 := by simp only [sub_re,one_re];linarith
  have source:=generatedRiemannZeta_zero_factorization owner (1-star c.value) (1-w)
    (ne_of_apply_ne Complex.re (by simpa only [zero_re] using positiveDual.ne'))
    (ne_of_apply_ne Complex.re (by simpa only [one_re] using belowDual.ne))
    (Gammaℝ_ne_zero_of_re_pos positiveDual)
  rw [generatedRiemannXiZeroOrder_one_sub,
    OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c] at source
  simpa only [generatedRiemannZeta_eq_mathlib,smul_eq_mul,
    show (1-w)-(1-star c.value)= -(w-star c.value) by ring] using source

/-- The source pole removes exactly one of the original m zero factors. -/
theorem actual_original_order_factor (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (positive : 0<w.re) (below : w.re<1) (apart : w≠star c.value) :
    mellin (wholeCountedRaw c) w/(w-star c.value)^(order c.value-1)=
      (-1:ℂ)^(order c.value)*bare (1-star c.value) (1-w)*mellin (companionWholeRaw c) (1-w) := by
  have mpositive:=original_order_positive c zero
  have power:(w-star c.value)^(order c.value)=
      (w-star c.value)^(order c.value-1)*(w-star c.value) := by
    conv_lhs=>rw [show order c.value=(order c.value-1)+1 by omega]
    rw [pow_succ]
  rw [actual_whole_mellin_value c zero w positive below apart,original_reverse_factor c w positive below,
    neg_eq_neg_one_mul,mul_pow,power]
  field_simp [sub_ne_zero.mpr apart,pow_ne_zero (order c.value-1) (sub_ne_zero.mpr apart)]

/-- This is the original m−1 leading finite part of the actual whole Fourier field. -/
theorem actual_original_order_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    Tendsto (fun w:ℂ=>mellin (wholeCountedRaw c) w/(w-star c.value)^(order c.value-1))
      (𝓝[≠](star c.value))
      (𝓝 ((-1:ℂ)^(order c.value+1)*bare (1-star c.value) (1-star c.value)*
        OriginalRieszFinitePairing.CoPoisson.Ward.ForcingPrimitive.leadingCoefficient c)) := by
  have realRead:(star c.value).re=c.value.re:=by simp only [star_def,conj_re]
  have positiveDual:0<(1-star c.value).re := by simp only [sub_re,one_re,realRead];linarith [c.belowOne]
  have belowDual:(1-star c.value).re<1 := by simp only [sub_re,one_re,realRead];linarith [c.rightHalf]
  have bareContinuous:ContinuousAt (bare (1-star c.value)) (1-star c.value) :=
    (divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum owner _ _ positiveDual belowDual).continuousAt
  have companionContinuous:=companion_mellin_continuous c zero (1-star c.value) (by linarith)
  have continuous:ContinuousAt (fun w:ℂ=>(-1:ℂ)^(order c.value)*
      bare (1-star c.value) (1-w)*mellin (companionWholeRaw c) (1-w)) (star c.value) :=
    (continuousAt_const.mul (bareContinuous.comp (continuousAt_const.sub continuousAt_id))).mul
      (companionContinuous.comp (continuousAt_const.sub continuousAt_id))
  have limit:Tendsto (fun w:ℂ=>(-1:ℂ)^(order c.value)*
      bare (1-star c.value) (1-w)*mellin (companionWholeRaw c) (1-w)) (𝓝[≠](star c.value))
      (𝓝 ((-1:ℂ)^(order c.value)*bare (1-star c.value) (1-star c.value)*
        mellin (companionWholeRaw c) (1-star c.value))) :=
    continuous.tendsto.mono_left nhdsWithin_le_nhds
  rw [actual_companion_resonant_moment c zero] at limit
  have normalized:(-1:ℂ)^(order c.value)*bare (1-star c.value) (1-star c.value)*
      (-OriginalRieszFinitePairing.CoPoisson.Ward.ForcingPrimitive.leadingCoefficient c)=
    (-1:ℂ)^(order c.value+1)*bare (1-star c.value) (1-star c.value)*
      OriginalRieszFinitePairing.CoPoisson.Ward.ForcingPrimitive.leadingCoefficient c := by
    rw [pow_succ]
    ring
  rw [normalized] at limit
  apply limit.congr'
  have strip:∀ᶠw:ℂ in 𝓝 (star c.value),0<w.re ∧ w.re<1 :=
    ((continuous_re.tendsto (star c.value)).eventually (Ioi_mem_nhds (by rw [realRead];linarith [c.rightHalf]))).and
      ((continuous_re.tendsto (star c.value)).eventually (Iio_mem_nhds (by rw [realRead];exact c.belowOne)))
  filter_upwards [strip.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w inside apart
  exact (actual_original_order_factor c zero w inside.1 inside.2 apart).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.FinitePart
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
