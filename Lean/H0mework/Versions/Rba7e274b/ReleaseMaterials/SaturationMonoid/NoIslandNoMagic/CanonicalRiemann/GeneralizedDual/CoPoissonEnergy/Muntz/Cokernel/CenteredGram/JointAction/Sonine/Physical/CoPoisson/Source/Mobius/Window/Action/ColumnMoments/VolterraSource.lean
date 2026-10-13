import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.WeightedEuler
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open OriginalRieszSource

def sourceTailPrice (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) : ℂ :=
  if lower<(1/4:ℝ) then weightedEndpointResponse coordinate lower else 0

-- The literal quarter response has an explicit whole Mellin tail, including its source endpoint constant.
theorem response_tail_source (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) (positive : 0<lower) :
    burnolRadiusMellinTailEvaluator lower positive (star coordinate.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) (wholeContactResponse coordinate)=sourceTailPrice coordinate lower := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  by_cases inside : lower<(1/4:ℝ)
  · rw [sourceTailPrice,if_pos inside,← original_response_weighted_band coordinate lower positive inside.le,
      intervalIntegral.integral_of_le inside.le,← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [burnolQuarterZeroExtension_coe (contactResponse coordinate)] with x extended
    change (wholeContactResponse coordinate:ℝ→ℂ) x=_ at extended
    by_cases lowerBound : lower<x
    · have xPositive : 0<x := positive.trans lowerBound
      rw [indicator_of_mem (show x∈Ioi lower from lowerBound),extended]
      by_cases quarter : x≤(1/4:ℝ)
      · rw [indicator_of_mem (show x∈symmetricInterval (1/4:ℝ) from ⟨by linarith,quarter⟩),
          indicator_of_mem (show x∈Ioc lower (1/4:ℝ) from ⟨lowerBound,quarter⟩)]
      · rw [indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun member=>quarter member.2),mul_zero,
          indicator_of_notMem (show x∉Ioc lower (1/4:ℝ) from fun member=>quarter member.2)]
    · rw [indicator_of_notMem (show x∉Ioi lower from lowerBound),indicator_of_notMem (show x∉Ioc lower (1/4:ℝ) from fun member=>lowerBound member.1)]
  · rw [sourceTailPrice,if_neg inside]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (burnolQuarterZeroExtension_coe (contactResponse coordinate)),ae_restrict_mem measurableSet_Ioi]
      with x extended after
    change wholeContactResponse coordinate x=_ at extended
    rw [extended,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun member=>not_lt_of_ge (le_trans member.2 (le_of_not_gt inside)) after),mul_zero]
    rfl

theorem response_pullback_tail (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) (lower : ℝ) (positive : 0<lower) :
    burnolRadiusMellinTailEvaluator lower positive (star coordinate.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) (F.fullPullback n (wholeContactResponse coordinate))=
      ((n:ℕ):ℂ)^(1-star coordinate.value)*sourceTailPrice coordinate (lower/(n:ℕ)) := by
  have nPositive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.property
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  have actualRead : (∫ t : ℝ in Ioi lower,(t:ℂ)^(-star coordinate.value)*F.fullPullback n (wholeContactResponse coordinate) t)=
      (∫ t : ℝ in Ioi lower,(t:ℂ)^(-star coordinate.value)*wholeContactResponse coordinate (t/(n:ℕ))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (full_pullback_read n (wholeContactResponse coordinate))] with t pulled
    rw [pulled]
  rw [actualRead]
  have source : (∫ x : ℝ in Ioi lower,(x:ℂ)^(-star coordinate.value)*wholeContactResponse coordinate (x/(n:ℕ)))=
      ((n:ℕ):ℂ)^(-star coordinate.value)*
        (∫ x : ℝ in Ioi lower,(((x/(n:ℕ)):ℝ):ℂ)^(-star coordinate.value)*wholeContactResponse coordinate (x/(n:ℕ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x after
    have xPositive : 0<x := positive.trans after
    have divisionPositive := div_pos xPositive nPositive
    have decomposed : (x:ℂ)=((n:ℕ):ℂ)*((x/(n:ℕ)):ℝ) := by push_cast;field_simp
    dsimp only
    rw [decomposed]
    have power := Complex.mul_cpow_ofReal_nonneg nPositive.le divisionPositive.le (r:=-star coordinate.value)
    simp only [Complex.ofReal_natCast] at power
    rw [power]
    ring
  rw [source]
  have moved : (∫ x : ℝ in Ioi lower,(((x/(n:ℕ)):ℝ):ℂ)^(-star coordinate.value)*wholeContactResponse coordinate (x/(n:ℕ)))=
      ((n:ℕ):ℂ)*(∫ y : ℝ in Ioi (lower/(n:ℕ)),(y:ℂ)^(-star coordinate.value)*wholeContactResponse coordinate y) := by
    have scaled := integral_comp_mul_left_Ioi
      (fun y : ℝ=>(y:ℂ)^(-star coordinate.value)*wholeContactResponse coordinate y)
      lower (inv_pos.mpr nPositive)
    simpa only [div_eq_mul_inv,mul_comm,inv_inv,Complex.real_smul,Complex.ofReal_natCast] using scaled
  rw [moved,← burnolRadiusMellinTailEvaluator_eq_integral (lower/(n:ℕ)) (div_pos positive nPositive)
    (star coordinate.value) (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf),response_tail_source]
  have power : ((n:ℕ):ℂ)^(-star coordinate.value)*((n:ℕ):ℂ)=((n:ℕ):ℂ)^(1-star coordinate.value) := by
    rw [show 1-star coordinate.value=-star coordinate.value+1 by ring,
      Complex.cpow_add _ _ (by exact_mod_cast n.ne_zero),Complex.cpow_one]
  rw [← mul_assoc,power]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
