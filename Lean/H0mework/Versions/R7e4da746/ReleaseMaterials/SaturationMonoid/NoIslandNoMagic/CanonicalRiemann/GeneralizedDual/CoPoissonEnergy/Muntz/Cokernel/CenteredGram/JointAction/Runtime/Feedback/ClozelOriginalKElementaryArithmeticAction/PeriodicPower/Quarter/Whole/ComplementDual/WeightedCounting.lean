import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.WeightedCounting
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
open scoped Topology InnerProductSpace
open private pweight pweight_summable channel channel_bound channel_summable forward_reindex
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private local_growth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction

def weightedQuarter (raw:ℝ→ℂ)
    (domain:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x) 2 μq):Hq :=
  domain.toLp (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x)

theorem actual_weighted_raw (raw:ℝ→ℂ)
    (domain:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x) 2 μq):
    (weightedQuarter raw domain:ℝ→ℂ)=ᵐ[μq]fun x:ℝ=>((|x|:ℝ):ℂ)*raw x :=
  domain.coeFn_toLp

def reverseTerm (weighted:Hq) (n:ℕ):BurnolL2 :=
  (((n+1:ℕ):ℂ)⁻¹) • ContinuousChannels.channel 1 (n+1:ℕ) (E weighted)

theorem actual_reverse_norm (weighted:Hq) (n:ℕ):
    ‖reverseTerm weighted n‖=((n+1:ℕ):ℝ)^(-(3/2:ℝ))*‖E weighted‖:=by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have scalar:(((n+1:ℕ):ℝ)⁻¹)*(Real.sqrt ((n+1:ℕ):ℝ))⁻¹=
      ((n+1:ℕ):ℝ)^(-(3/2:ℝ)):=by
    rw [←Real.rpow_neg_one,Real.sqrt_eq_rpow,←Real.rpow_neg positive.le,←Real.rpow_add positive]
    congr 1
    norm_num
  simp only [reverseTerm,ContinuousChannels.channel,norm_smul,norm_inv,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (burnolMultiplicativeDilation _).norm_map]
  rw [←mul_assoc,scalar]

theorem actual_reverse_summable (weighted:Hq):
    Summable (fun n:ℕ=>‖reverseTerm weighted n‖):=by
  have power:Summable (fun n:ℕ=>(n:ℝ)^(-(3/2:ℝ))):=
    Real.summable_nat_rpow.mpr (by norm_num)
  have shifted:Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^(-(3/2:ℝ))):=
    (summable_nat_add_iff 1).mpr power
  simpa only [actual_reverse_norm] using shifted.mul_right ‖E weighted‖

def reverseCount (weighted:Hq):BurnolL2:=∑'n:ℕ,reverseTerm weighted n

private def priceTerm (raw:ℝ→ℂ) (c:BurnolCompletedMellinCoordinate) (n:ℕ) (x:ℝ):ℂ:=
  star (raw x)*channel (regularLocal c) n x

private theorem price_envelope (raw:ℝ→ℂ) (c:BurnolCompletedMellinCoordinate)
    (L:ℝ) (nonnegative:0≤L) (growth:∀x:ℝ,‖regularLocal c x‖≤L*|x|)
    (n:ℕ) (x:ℝ) (inside:x∈symmetricInterval q):
    ‖priceTerm raw c n x‖≤(L*q*pweight n)*‖raw x‖:=by
  have bound:‖channel (regularLocal c) n x‖≤L*q*pweight n:=by
    apply (channel_bound _ L growth n x).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (abs_le.mpr inside) nonnegative) (by unfold pweight;positivity)
  rw [priceTerm,norm_mul,norm_star]
  exact (mul_le_mul_of_nonneg_left bound (norm_nonneg _)).trans_eq (by ring)

private theorem price_integrable (raw:ℝ→ℂ) (integrable:Integrable raw μq)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (n:ℕ):
    Integrable (priceTerm raw c n) μq:=by
  obtain ⟨L,nonnegative,lip⟩:=actual_regular_local_lipschitz c
  have growth:=local_growth c zero L lip
  have regular:Continuous (channel (regularLocal c) n):=
    continuous_const.mul ((actual_regular_local_continuous c).comp (continuous_id.div_const _))
  apply (integrable.norm.const_mul (L*q*pweight n)).mono'
    (integrable.aestronglyMeasurable.star.mul regular.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact price_envelope raw c L nonnegative growth n x inside

private theorem price_norm_summable (raw:ℝ→ℂ) (integrable:Integrable raw μq)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Summable (fun n:ℕ=>∫x:ℝ,‖priceTerm raw c n x‖ ∂μq):=by
  obtain ⟨L,nonnegative,lip⟩:=actual_regular_local_lipschitz c
  have growth:=local_growth c zero L lip
  apply (pweight_summable.mul_left (L*q*(∫x:ℝ,‖raw x‖ ∂μq))).of_nonneg_of_le
    (fun n=>integral_nonneg (fun x=>norm_nonneg _))
  intro n
  calc
    _≤∫x:ℝ,(L*q*pweight n)*‖raw x‖ ∂μq:=by
      apply integral_mono_ae (price_integrable raw integrable c zero n).norm
        (integrable.norm.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
      exact price_envelope raw c L nonnegative growth n x inside
    _=_:=by rw [integral_const_mul];ring

private theorem actual_term_price (raw:ℝ→ℂ)
    (domain:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x) 2 μq)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (n:ℕ):
    inner ℂ (reverseTerm (weightedQuarter raw domain) n) (E (normalizedRegular c zero))=
      ∫x:ℝ,priceTerm raw c n x ∂μq:=by
  let N:ℝ:=(n+1:ℕ)
  have positive:0<N:=by dsimp [N];positivity
  have large:1≤N:=by dsimp [N];exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have paired:=congrArg star (ContinuousChannels.channel_pairing N
    (E (normalizedRegular c zero)) (E (weightedQuarter raw domain)))
  simp only [star_def,inner_conj_symm] at paired
  rw [reverseTerm,inner_smul_left]
  simp only [starRingEnd_apply,star_inv₀,star_natCast]
  rw [←paired,show E=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_left,
    ←show E=burnolQuarterRestriction.adjoint from rfl,←WholeSourceWindow.window_channel]
  rw [L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [actual_weighted_raw raw domain,
    countingWindow_raw N positive (normalizedRegular c zero) (normalizedRegularRaw c)
      (actual_normalized_raw c zero),ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne (0:ℝ)),ae_restrict_of_ae (volume.ae_ne q),
    ae_restrict_of_ae (volume.ae_ne (-q))] with x weighted counted inside nonzero right left
  have innerGap:|x|<q:=abs_lt.mpr
    ⟨lt_of_le_of_ne inside.1 (Ne.symm left),lt_of_le_of_ne inside.2 right⟩
  have moved:|x/N|<q:=by
    rw [abs_div,abs_of_pos positive]
    exact (div_le_self (abs_nonneg x) large).trans_lt innerGap
  have window:x/N∈symmetricInterval q:=abs_le.mp moved.le
  have regular:x/N∈Ioo (-q) q:=abs_lt.mp moved
  rw [RCLike.inner_apply,starRingEnd_apply,weighted,counted]
  simp only [countingRaw,indicator_of_mem window,normalizedRegularRaw,regularCompactRaw,
    indicator_of_mem regular,star_mul,star_def,Complex.conj_ofReal,
    abs_div,abs_of_pos positive,Complex.ofReal_div]
  rw [priceTerm,channel]
  simp only [star_def]
  dsimp only [N]
  field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]

/-- A genuinely L¹ dual is counted through its paid |x|-weighted L² field. -/
theorem actual_l1_weighted_native_price (raw:ℝ→ℂ) (integrable:Integrable raw μq)
    (domain:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x) 2 μq)
    (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (reverseCount (weightedQuarter raw domain)) (E (normalizedRegular c zero))=
      ∫x:ℝ,star (raw x)*quarterBankRaw c x ∂μq:=by
  have left:HasSum (fun n:ℕ=>inner ℂ (reverseTerm (weightedQuarter raw domain) n)
      (E (normalizedRegular c zero)))
      (inner ℂ (reverseCount (weightedQuarter raw domain)) (E (normalizedRegular c zero))):=
    (actual_reverse_summable _).of_norm.hasSum.mapL (innerSLFlip ℂ (E (normalizedRegular c zero)))
  have right:=hasSum_integral_of_summable_integral_norm
    (fun n=>price_integrable raw integrable c zero n) (price_norm_summable raw integrable c zero)
  have whole:(∫x:ℝ,(∑'n:ℕ,priceTerm raw c n x) ∂μq)=
      ∫x:ℝ,star (raw x)*quarterBankRaw c x ∂μq:=by
    apply integral_congr_ae
    filter_upwards with x
    simp only [priceTerm,quarterBankRaw,forward_reindex,tsum_mul_left]
  rw [whole] at right
  exact HasSum.unique (left.congr_fun (fun n=>(actual_term_price raw domain c zero n).symm)) right

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.WeightedCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
