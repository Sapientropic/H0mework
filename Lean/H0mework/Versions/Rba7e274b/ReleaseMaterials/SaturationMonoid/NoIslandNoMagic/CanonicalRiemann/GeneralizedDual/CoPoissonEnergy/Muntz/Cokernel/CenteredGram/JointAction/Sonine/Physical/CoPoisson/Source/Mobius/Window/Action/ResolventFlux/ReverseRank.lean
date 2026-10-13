import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.RankOne
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Reverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace

def fullS : BurnolL2 →L[ℂ] BurnolL2 := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n • fullPullback n

def sigma : ℂ := ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,coefficient n

def exteriorMoment (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf (fullS value)

def interiorBase (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate (1/4:ℝ) (by norm_num))

theorem lower_full_source (value : BurnolL2) : M value=cutoff 4 (fullS value)-(sigma*actualMean value) • box 4 := by
  rw [lower_source_cutoff]
  unfold fullS sigma
  simp only [sum_apply,smul_apply,map_sum,map_smul]
  simp only [smul_sub,smul_smul]
  rw [Finset.sum_sub_distrib,Finset.sum_mul,Finset.sum_smul]

 theorem fullS_Rplus (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    fullS (Rplus z value)=Rplus z (fullS value) := by
  unfold Rplus
  rw [map_neg,← fullS.integral_comp_comm (Rplus_integrable z rightQuarter value)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  unfold RplusIntegrand
  dsimp only
  rw [map_smul]
  congr 1
  unfold fullS
  simp only [sum_apply,smul_apply,map_sum,map_smul,full_pullback_action]

 theorem fullS_even (value : Ambient) : reflectL2 (fullS (value : BurnolL2))=fullS (value : BurnolL2) := by
  unfold fullS
  simp only [sum_apply,smul_apply,map_sum,map_smul,fullPullback,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,reflectL2_burnolMultiplicativeDilation]
  rw [mem_evenL2ClosedFace_iff.mp value.property.2]

 theorem cutoff_even (value : BurnolL2) (even : reflectL2 value=value) : reflectL2 (cutoff 4 value)=cutoff 4 value := by
  apply Lp.ext
  have moved := negMeasurePreserving.quasiMeasurePreserving.ae_eq (cutoff_read 4 value)
  have parity := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change (reflectL2 value : ℝ→ℂ) =ᵐ[volume] (value : ℝ→ℂ) ∘ (fun x=>-x) at parity
  rw [even] at parity
  filter_upwards [Lp.coeFn_compMeasurePreserving (cutoff 4 value) negMeasurePreserving,
    moved,cutoff_read 4 value,parity] with x reflected moved direct equal
  simp only [Function.comp_def] at moved equal
  rw [show reflectL2 (cutoff 4 value) x=(cutoff 4 value : BurnolL2) (-x) from reflected,moved,direct]
  have membership : -x∈symmetricInterval 4 ↔ x∈symmetricInterval 4 := by
    change -4≤-x ∧ -x≤4 ↔ -4≤x ∧ x≤4
    constructor <;> rintro ⟨lower,upper⟩ <;> constructor <;> linarith
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside,indicator_of_mem (membership.mpr inside)]
    exact equal.symm
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside (membership.mp h))]

 theorem Rplus_even (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) : reflectL2 (Rplus (coordinate.value/2) value)=Rplus (coordinate.value/2) value := by
  unfold Rplus
  rw [map_neg,← reflectL2.integral_comp_comm (RplusIntegrand (coordinate.value/2) value)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  unfold RplusIntegrand
  dsimp only
  rw [map_smul,reflectL2_burnolMultiplicativeDilation,even]

 theorem interior_base_read (coordinate : BurnolCompletedMellinCoordinate) :
    (interiorBase coordinate : ℝ→ℂ)=ᵐ[volume] fun x=>if |x| < (4:ℝ) then -((|x|:ℝ):ℂ)^(coordinate.value-1) else 0 := by
  let base := burnolRadiusNormalizedUnitTail coordinate (1/4:ℝ) (by norm_num)
  have raw := burnolRadiusUnitTail_coeFn coordinate (1/4:ℝ) (by norm_num)
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp base) ((Lp.memLp base).ae_eq raw) raw
  filter_upwards [burnolTateReciprocalL2_coeFn base,pulled,volume.ae_ne (0:ℝ)] with x actual inverse nonzero
  change burnolTateReciprocalL2 base x=_
  rw [actual,inverse]
  unfold burnolTateReciprocalRaw
  dsimp only
  rw [abs_inv]
  have positive := abs_pos.mpr nonzero
  have condition : (1/4:ℝ) < |x|⁻¹ ↔ |x| < 4 := by
    rw [inv_eq_one_div,lt_div_iff₀ positive]
    constructor <;> intro bound <;> linarith
  simp only [condition]
  by_cases inside : |x| < (4:ℝ)
  · rw [if_pos inside,if_pos inside,Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (abs_nonneg x),Complex.cpow_neg,inv_inv,mul_neg]
    congr 1
    rw [← Complex.cpow_neg_one,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  · rw [if_neg inside,if_neg inside,mul_zero]


-- A real outer source supports the one exterior moment before reciprocal transport.
theorem outer_tail_fixed (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (t : ℝ) (positive : 0<t) (small : t≤4) :
    burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf (outerCut value)=
      burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,burnolRadiusMellinTailEvaluator_eq_integral]
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub value (cutoff 4 value),cutoff_read 4 value] with x subtraction cutRead
  change (Ioi t).indicator (fun x => (x:ℂ)^(-coordinate.value)*(outerCut value : BurnolL2) x) x=_
  by_cases outer : (4:ℝ)<x
  · rw [indicator_of_mem (show x∈Ioi t from small.trans_lt outer),indicator_of_mem (show x∈Ioi 4 from outer)]
    change (x:ℂ)^(-coordinate.value)*(value-cutoff 4 value : BurnolL2) x=_
    rw [subtraction,Pi.sub_apply,cutRead,indicator_of_notMem (show x∉symmetricInterval 4 from fun h=>not_le_of_gt outer h.2),sub_zero]
  · rw [indicator_of_notMem (show x∉Ioi 4 from outer)]
    by_cases after : t<x
    · rw [indicator_of_mem (show x∈Ioi t from after)]
      change (x:ℂ)^(-coordinate.value)*(value-cutoff 4 value : BurnolL2) x=0
      rw [subtraction,Pi.sub_apply,cutRead,indicator_of_mem (show x∈symmetricInterval 4 from ⟨by linarith,le_of_not_gt outer⟩),sub_self,mul_zero]
    · rw [indicator_of_notMem (show x∉Ioi t from after)]

 theorem Rplus_outer_positive_profile (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ∀ᵐ t : ℝ ∂volume, ∀ _positive : 0<t, ∀ _small : t≤4,
      Rplus (coordinate.value/2) (outerCut value) t=
      -(2:ℂ)*(t:ℂ)^(coordinate.value-1)*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value := by
  have source := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile coordinate (outerCut value)
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have same : OriginalPaPhysicalGreen.sourceVolterraResolvent coordinate (outerCut value)=Rplus (coordinate.value/2) (outerCut value) := by
    exact (Rplus_tate _ right _).symm
  rw [same] at source
  filter_upwards [source] with t read positive small
  rw [read positive,outer_tail_fixed coordinate value t positive small]

 theorem cutoff_Rplus_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    cutoff 4 (Rplus (coordinate.value/2) (cutoff 4 value))=Rplus (coordinate.value/2) (cutoff 4 value) := by
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  unfold Rplus
  rw [map_neg,← (cutoff 4).integral_comp_comm (Rplus_integrable _ right (cutoff 4 value))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau positive
  unfold RplusIntegrand
  dsimp only
  rw [map_smul,action_cutoff 4 (by norm_num)]
  have bounded : 4*Real.exp (-(tau/2))≤(4:ℝ) := by
    have tauPositive : 0<tau := positive
    have scale : Real.exp (-(tau/2))≤1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  congr 1
  apply Lp.ext
  filter_upwards [cutoff_read 4 (cutoff (4*Real.exp (-(tau/2))) (burnolMultiplicativeDilation (tau/2) value)),
    cutoff_read (4*Real.exp (-(tau/2))) (burnolMultiplicativeDilation (tau/2) value)] with x twice once
  rw [twice]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,once,indicator_of_notMem]
    intro small
    exact inside ⟨by linarith [small.1],by linarith [small.2]⟩

 theorem cutoff_Rplus_difference (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    cutoff 4 (Rplus (coordinate.value/2) value)-Rplus (coordinate.value/2) (cutoff 4 value)=
      cutoff 4 (Rplus (coordinate.value/2) (outerCut value)) := by
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  unfold outerCut
  simp only [sub_apply,ContinuousLinearMap.id_apply]
  rw [Rplus_sub _ right,map_sub,cutoff_Rplus_source]

 theorem cutoff_Rplus_rank (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    cutoff 4 (Rplus (coordinate.value/2) value)-Rplus (coordinate.value/2) (cutoff 4 value)=
      (2*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value) • interiorBase coordinate := by
  rw [cutoff_Rplus_difference]
  have outerEven : reflectL2 (outerCut value)=outerCut value := by
    unfold outerCut
    simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,even,cutoff_even value even]
  let field := Rplus (coordinate.value/2) (outerCut value)
  have parity := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  change (reflectL2 field : ℝ→ℂ)=ᵐ[volume] (field : ℝ→ℂ) ∘ (fun x=>-x) at parity
  rw [Rplus_even coordinate (outerCut value) outerEven] at parity
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae (Rplus_outer_positive_profile coordinate value)
  apply Lp.ext
  filter_upwards [cutoff_read 4 field,Lp.coeFn_smul (2*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value) (interiorBase coordinate),
    interior_base_read coordinate,Rplus_outer_positive_profile coordinate value,negative,parity,volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x cutRead scalar basis direct reverse reflected nonzero notFour notNegativeFour
  change (cutoff 4 field : BurnolL2) x=_
  rw [cutRead,scalar]
  change (symmetricInterval 4).indicator (field : ℝ→ℂ) x=(2*burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value)*interiorBase coordinate x
  rw [basis]
  by_cases inside : |x|<(4:ℝ)
  · rw [indicator_of_mem (show x∈symmetricInterval 4 from abs_le.mp inside.le),if_pos inside]
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · rw [abs_of_neg neg]
      have read : field x=field (-x) := reflected
      rw [read,reverse (by linarith) (by linarith [abs_of_neg neg ▸ inside])]
      ring
    · rw [abs_of_pos pos,direct pos (by simpa only [abs_of_pos pos] using inside.le)]
      ring
  · have outside : (4:ℝ) < |x| := by
      have unequal : |x|≠4 := by
        intro equal
        rcases eq_or_eq_neg_of_abs_eq equal with same | same
        · exact notFour same
        · exact notNegativeFour same
      exact lt_of_le_of_ne (le_of_not_gt inside) unequal.symm
    rw [indicator_of_notMem (show x∉symmetricInterval 4 from fun h=>not_le_of_gt outside (abs_le.mpr h)),if_neg inside,mul_zero]

-- The complete reverse reaction has one tail source and the two actual mean terms.
def reverseRankSource (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  (2*exteriorMoment coordinate value) • interiorBase coordinate-
  (sigma*actualMean (Rplus (coordinate.value/2) value)) • box 4+
  (sigma*actualMean value) • Rplus (coordinate.value/2) (box 4)

 theorem source_reverse_flux_three_base (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    reverseFlux (coordinate.value/2) (value : BurnolL2)=reverseRankSource coordinate (value : BurnolL2) := by
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have source := actual_M_Rplus_action (coordinate.value/2) right (value : BurnolL2)
  rw [lower_full_source,lower_full_source,fullS_Rplus _ right,Rplus_sub _ right,Rplus_smul _ _ right] at source
  unfold reverseRankSource exteriorMoment
  rw [← cutoff_Rplus_rank coordinate (fullS (value : BurnolL2)) (fullS_even value)]
  calc
    _ = (cutoff 4 (Rplus (coordinate.value/2) (fullS (value : BurnolL2)))-
      (sigma*actualMean (Rplus (coordinate.value/2) (value : BurnolL2))) • box 4)-
      (Rplus (coordinate.value/2) (cutoff 4 (fullS (value : BurnolL2)))-
      (sigma*actualMean (value : BurnolL2)) • Rplus (coordinate.value/2) (box 4)) := by
        rw [source]
        module
    _ = _ := by module

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
