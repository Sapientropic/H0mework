import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.WindowMoment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalUnitMellinSource.Band
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder OriginalUnitXiConjugateOrderSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "test" => OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest
open private coordinate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder

def massRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  if |x|<q*Real.exp h then star (F (test c h) x) else 0
def powerMomentRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  if |x|<q*Real.exp h then star (F (test c h) x)*((|x|:ℝ):ℂ)^(star c.value-1) else 0
def logBandRaw (c:BurnolCompletedMellinCoordinate) (h:ℝ) (j:Nat) (x:ℝ) : ℂ :=
  if q < |x| ∧ |x|<q*Real.exp h then
    star (F (test c h) x)*((|x|:ℝ):ℂ)^(star c.value-1)*(bandLog |x|)^j else 0
def fullMass (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ := ∫ x:ℝ,massRaw c h x
def fullLogBand (c:BurnolCompletedMellinCoordinate) (h:ℝ) (j:Nat) : ℂ := ∫ x:ℝ,logBandRaw c h j x

private theorem mass_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ) : Integrable (massRaw c h) := by
  let r:=q*Real.exp h
  have finite:volume (Ioo (-r) r)≠⊤:=by simp
  let box:BurnolL2:=indicatorConstLp 2 measurableSet_Ioo finite (1:ℂ)
  have raw:(box:ℝ→ℂ)=ᵐ[volume](Ioo (-r) r).indicator (fun _=>(1:ℂ)):=
    indicatorConstLp_coeFn
  apply (L2.integrable_inner (𝕜:=ℂ) (F (test c h)) box).congr
  filter_upwards [raw] with x source
  rw [RCLike.inner_apply,starRingEnd_apply,source]
  unfold massRaw
  by_cases inside:|x|<r
  · rw [indicator_of_mem (show x∈Ioo (-r) r from abs_lt.mp inside),if_pos inside,one_mul]
  · rw [indicator_of_notMem (show x∉Ioo (-r) r from fun hx=>inside (abs_lt.mpr hx)),
      if_neg inside,zero_mul]

private theorem power_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ) : Integrable (powerMomentRaw c h) := by
  apply (L2.integrable_inner (𝕜:=ℂ) (F (test c h)) (powerWindow c h)).congr
  filter_upwards [actual_power_window_raw c h] with x source
  rw [RCLike.inner_apply,starRingEnd_apply,source]
  unfold powerMomentRaw
  split_ifs <;> simp only [mul_comm,zero_mul]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "reflected" => conjugateZeroObservation observation
local notation "rh" => conjugateHalf observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner reflected
local notation "top" => ((burnolDirectRightResolventCLM (barC c))^m) (burnolUnitTailResponse (barC c) 4)
include nontrivial

private theorem original_top_raw :
    ∀ᵐ x:ℝ ∂volume, |x|<2*q → F top x=
      bandMean (barC c) m+((|x|:ℝ):ℂ)^(star (c).value-1)*
        ((if q < |x| then bandCoefficient m*(bandLog |x|)^m else 0)-2*e) := by
  have same:burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down=barC c := by
    apply coordinate_eq
    rfl
  have order:=actual_original_Xi_order_conjugate c
  change generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate=m at order
  have source:=actual_full_top_raw reflected (observation.conjugate_nontrivial nontrivial) rh
  unfold fullTopRaw at source
  change ∀ᵐ x:ℝ ∂volume, |x|<2*q →
    F (((burnolDirectRightResolventCLM (burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down))^
      (generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate))
      (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down) 4)) x=_ at source
  rw [same,order] at source
  exact source

private theorem complete_integrand (h:ℝ) (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    (fun x:ℝ=>inner ℂ (F (test c h) x) (F top x))=ᵐ[volume]
      fun x=>bandMean (barC c) m*massRaw c h x+(-2*e)*powerMomentRaw c h x+
        bandCoefficient m*logBandRaw c h m x := by
  filter_upwards [original_top_raw observation nontrivial half,
    actual_transformed_outside c h nonnegative,volume.ae_ne (q*Real.exp h),volume.ae_ne (-(q*Real.exp h))]
    with x source outside notPositive notNegative
  change q*Real.exp h < |x| → F (test c h) x=0 at outside
  have notEdge:|x|≠q*Real.exp h:=by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with same|same
    · exact notPositive same
    · exact notNegative same
  simp only [RCLike.inner_apply,starRingEnd_apply]
  unfold massRaw powerMomentRaw logBandRaw
  by_cases inside:|x|<q*Real.exp h
  · rw [if_pos inside,if_pos inside,source (inside.trans bound)]
    by_cases after:q < |x|
    · rw [if_pos after,if_pos ⟨after,inside⟩]
      ring
    · rw [if_neg after,if_neg (fun both=>after both.1)]
      ring
  · have beyond:q*Real.exp h < |x|:=lt_of_le_of_ne (le_of_not_gt inside) notEdge.symm
    rw [if_neg inside,if_neg inside,if_neg (fun both=>inside both.2),outside beyond,star_zero,mul_zero]
    ring

private theorem log_integrable (h:ℝ) (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    Integrable (logBandRaw c h m) := by
  have integrable:=((L2.integrable_inner (𝕜:=ℂ) (F (test c h)) (F top)).sub
    ((mass_integrable c h).const_mul (bandMean (barC c) m))).sub
      ((power_integrable c h).const_mul (-2*e))
  have coefficient:bandCoefficient m≠0:=by
    unfold bandCoefficient
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  apply (integrable.const_mul (bandCoefficient m)⁻¹).congr
  filter_upwards [complete_integrand observation nontrivial half h nonnegative bound] with x source
  simp only [Pi.sub_apply]
  rw [source]
  field_simp [coefficient]
  ring

/-- The original m-order transformed price has its complete mean, exact Xi/self price, and logarithmic band. -/
theorem actual_original_order_full_price (h:ℝ) (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    inner ℂ (test c h) top=
      bandMean (barC c) m*fullMass c h+
      (-2*e)*(((8:ℂ)*(16:ℂ)^(-star (c).value))*
        star ((reciprocalMellinTranslationCharacter (c).value h-(Real.exp (h/2):ℂ))*kernelSelfSource c))+
      bandCoefficient m*fullLogBand c h m := by
  rw [←fourierL2.inner_map_map,L2.inner_def,
    integral_congr_ae (complete_integrand observation nontrivial half h nonnegative bound)]
  have massPaid:Integrable (fun x:ℝ=>bandMean (barC c) m*massRaw c h x):=
    (mass_integrable c h).const_mul (bandMean (barC c) m)
  have powerPaid:Integrable (fun x:ℝ=>(-2*e)*powerMomentRaw c h x):=
    (power_integrable c h).const_mul (-2*e)
  have logPaid:Integrable (fun x:ℝ=>bandCoefficient m*logBandRaw c h m x):=
    (log_integrable observation nontrivial half h nonnegative bound).const_mul (bandCoefficient m)
  have sumPaid:=integral_add (massPaid.add powerPaid) logPaid
  simp only [Pi.add_apply] at sumPaid
  rw [sumPaid,integral_add massPaid powerPaid,
    integral_const_mul,integral_const_mul,integral_const_mul]
  change _+(-2*e)*(∫ x:ℝ,powerMomentRaw c h x)+_=_
  rw [show (∫ x:ℝ,powerMomentRaw c h x)=
    ((8:ℂ)*(16:ℂ)^(-star (c).value))*
      star ((reciprocalMellinTranslationCharacter (c).value h-(Real.exp (h/2):ℂ))*kernelSelfSource c)
    from actual_radius_power_moment c h nonnegative]
  rfl

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
