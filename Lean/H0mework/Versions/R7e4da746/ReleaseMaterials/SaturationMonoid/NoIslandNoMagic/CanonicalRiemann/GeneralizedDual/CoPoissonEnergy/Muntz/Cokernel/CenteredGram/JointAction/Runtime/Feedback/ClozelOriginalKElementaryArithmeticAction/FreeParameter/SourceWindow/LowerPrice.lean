import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.FullPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.LowerPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalUnitMellinSource.Band OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder OriginalUnitXiConjugateOrderSource
open scoped Topology InnerProductSpace
open private coordinate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder
open private mass_integrable log_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.FullPrice
local notation "q" => (1/4 : ℝ)
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "test" => OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest

private theorem lower_full_raw (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (j : Nat)
    (before : j<generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate) :
    let d:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
    ∀ᵐ x : ℝ ∂volume, |x|<2*q → F (unitPower observation half j) x=
      bandMean d j+((|x|:ℝ):ℂ)^(d.value-1)*
        (if q< |x| then bandCoefficient j*(bandLog |x|)^j else 0) := by
  dsimp only
  let d:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let u:=unitPower observation half j
  have quarter := OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource.actual_fourier_quarter_power observation nontrivial half j before
  change burnolQuarterRestriction (F u)=bandMean d j • intervalConstant q at quarter
  have small : ∀ᵐ x : ℝ ∂volume, |x|≤q → F u x=bandMean d j := by
    have localRead : (F u:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] fun _=>bandMean d j := by
      filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F u),
        Lp.coeFn_smul (bandMean d j) (intervalConstant q),intervalConstant_coeFn q] with x restricted scalar constant
      have source := congrArg (fun value : BurnolQuarterIntervalL2=>value x) quarter
      change burnolQuarterRestriction (F u) x=F u x at restricted
      rw [restricted,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one] at source
      exact source
    have globalRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp localRead
    filter_upwards [globalRead] with x source inside
    exact source (abs_le.mp inside)
  have direct := actual_fourier_first_cell_power observation nontrivial half j before
  have opposite := negMeasurePreserving.quasiMeasurePreserving.ae direct
  have even : reflectL2 (F u)=F u := by
    rw [←fourierL2_reflectL2_commute]
    have source := mem_evenL2ClosedFace_iff.mp (unitPower_physical observation nontrivial half j before).2
    rw [source]
  have parity := Lp.coeFn_compMeasurePreserving (F u) negMeasurePreserving
  change (reflectL2 (F u):ℝ→ℂ)=ᵐ[volume] fun x=>F u (-x) at parity
  rw [even] at parity
  filter_upwards [small,direct,opposite,parity] with x inside positive negative parity bound
  by_cases quarter : |x|≤q
  · rw [inside quarter,if_neg (not_lt_of_ge quarter),mul_zero,add_zero]
  · have after : q< |x| := lt_of_not_ge quarter
    rw [if_pos after]
    by_cases sign : 0≤x
    · rw [abs_of_nonneg sign] at after bound ⊢
      rw [positive after bound]
      ring
    · have sign : x<0 := lt_of_not_ge sign
      rw [abs_of_neg sign] at after bound ⊢
      rw [parity]
      change F (unitPower observation half j) (-x)=_
      rw [negative after bound]
      ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "reflected" => conjugateZeroObservation observation
local notation "rh" => conjugateHalf observation half
local notation "u" j => ((burnolDirectRightResolventCLM (barC c))^j) (burnolUnitTailResponse (barC c) 4)
include nontrivial

private theorem original_lower_raw (j : Nat) (before : j<m) :
    ∀ᵐ x : ℝ ∂volume, |x|<2*q → F (u j) x=
      bandMean (barC c) j+((|x|:ℝ):ℂ)^(star (c).value-1)*
        (if q< |x| then bandCoefficient j*(bandLog |x|)^j else 0) := by
  have same : burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down=barC c := by
    apply coordinate_eq
    rfl
  have order := actual_original_Xi_order_conjugate c
  change generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate=m at order
  have lower : j<generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate := by rwa [order]
  have source := lower_full_raw reflected (observation.conjugate_nontrivial nontrivial) rh j lower
  dsimp only at source
  change ∀ᵐ x : ℝ ∂volume, |x|<2*q →
    F (((burnolDirectRightResolventCLM (burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down))^j)
      (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate reflected (rh).down) 4)) x=_ at source
  rw [same] at source
  exact source

private theorem lower_integrand (j : Nat) (before : j<m) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    (fun x : ℝ=>inner ℂ (F (test c h) x) (F (u j) x))=ᵐ[volume]
      fun x=>bandMean (barC c) j*massRaw c h x+bandCoefficient j*logBandRaw c h j x := by
  filter_upwards [original_lower_raw observation nontrivial half j before,
    actual_transformed_outside c h nonnegative,volume.ae_ne (q*Real.exp h),volume.ae_ne (-(q*Real.exp h))]
    with x source outside neEdge neMinusEdge
  have notEdge : |x|≠q*Real.exp h := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with same|same
    · exact neEdge same
    · exact neMinusEdge same
  change q*Real.exp h< |x| → F (test c h) x=0 at outside
  rw [RCLike.inner_apply,starRingEnd_apply]
  unfold massRaw logBandRaw
  by_cases inside : |x|<q*Real.exp h
  · rw [if_pos inside,source (inside.trans bound)]
    by_cases after : q< |x|
    · rw [if_pos after,if_pos ⟨after,inside⟩]
      ring
    · rw [if_neg after,if_neg (fun both=>after both.1)]
      ring
  · have beyond : q*Real.exp h< |x| := lt_of_le_of_ne (le_of_not_gt inside) notEdge.symm
    rw [if_neg inside,if_neg (fun both=>inside both.2),outside beyond,star_zero,mul_zero]
    ring

theorem actual_original_lower_log_integrable (j : Nat) (before : j<m) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) : Integrable (logBandRaw c h j) := by
  have source := (L2.integrable_inner (𝕜:=ℂ) (F (test c h)) (F (u j))).sub
    ((mass_integrable c h).const_mul (bandMean (barC c) j))
  have coefficient : bandCoefficient j≠0 := by
    unfold bandCoefficient
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  apply (source.const_mul (bandCoefficient j)⁻¹).congr
  filter_upwards [lower_integrand observation nontrivial half j before h nonnegative bound] with x read
  simp only [Pi.sub_apply]
  rw [read]
  field_simp [coefficient]
  ring

theorem actual_original_lower_price (j : Nat) (before : j<m) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    inner ℂ (test c h) (u j)=
      bandMean (barC c) j*fullMass c h+bandCoefficient j*fullLogBand c h j := by
  rw [←fourierL2.inner_map_map,L2.inner_def,
    integral_congr_ae (lower_integrand observation nontrivial half j before h nonnegative bound)]
  have massPaid : Integrable (fun x=>bandMean (barC c) j*massRaw c h x) :=
    (mass_integrable c h).const_mul _
  have logPaid : Integrable (fun x=>bandCoefficient j*logBandRaw c h j x) :=
    (actual_original_lower_log_integrable observation nontrivial half j before h nonnegative bound).const_mul _
  rw [integral_add massPaid logPaid,integral_const_mul,integral_const_mul]
  rfl

theorem actual_original_log_integrable (j : Nat) (before : j≤m) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) : Integrable (logBandRaw c h j) := by
  rcases before.eq_or_lt with same|lower
  · subst j
    exact log_integrable observation nontrivial half h nonnegative bound
  · exact actual_original_lower_log_integrable observation nontrivial half j lower h nonnegative bound

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.LowerPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
