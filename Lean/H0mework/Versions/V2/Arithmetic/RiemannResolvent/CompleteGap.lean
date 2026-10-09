import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CompleteRemainder

/-! The full resolvent source preserves its inner gap and parity at every order. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

local instance firstSourceAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem dilation_innerGap (value : BurnolL2)
    (gap : (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (shift : ℝ) (nonpositive : shift ≤ 0) :
    (burnolMultiplicativeDilation shift value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  have sourceGlobal := (ae_restrict_iff'
    (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp gap
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  filter_upwards [ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value),
    ae_restrict_of_ae (qmp.ae sourceGlobal),
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
      with x hvalue hsource hx
  have small : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr hx
  have scaledSmall : |Real.exp shift * x| ≤ (1 / 4 : ℝ) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos shift)]
    exact (mul_le_of_le_one_left (abs_nonneg x)
      (Real.exp_le_one_iff.mpr nonpositive)).trans small
  rw [hvalue]
  unfold burnolL2RawNormalizedDilation
  rw [hsource (abs_le.mp scaledSmall), mul_zero]

private theorem restriction_zero_of_gap (value : BurnolL2)
    (gap : (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0) :
    burnolRadiusRestriction (1 / 4) value = 0 := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ)) value,
    gap, Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval (1 / 4 : ℝ)))]
      with x hread hzero htarget
  have read : burnolRadiusRestriction (1 / 4) value x = value x := hread
  rw [read, hzero, htarget]
  rfl

theorem burnolDirectRightResolvent_innerGap (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : BurnolL2)
    (gap : (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0) :
    burnolRadiusRestriction (1 / 4) (burnolDirectRightResolvent z value) = 0 := by
  have integrable := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value
  unfold burnolDirectRightResolvent
  rw [map_neg, ← (burnolRadiusRestriction (1 / 4)).integral_comp_comm integrable]
  have sourceZero : (fun h : ℝ => burnolRadiusRestriction (1 / 4)
      (burnolDirectRightResolventIntegrand z value h)) =ᵐ[volume.restrict (Ioi 0)] fun _ => 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul, restriction_zero_of_gap _
      (dilation_innerGap value gap (-h / 2) (by
        have positive : 0 < h := hh
        linarith)), smul_zero]
  rw [integral_congr_ae sourceZero, integral_zero, neg_zero]

private theorem gap_of_restriction_zero (value : BurnolL2)
    (zero : burnolRadiusRestriction (1 / 4) value = 0) :
    (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ)) value,
    Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval (1 / 4 : ℝ)))] with x hread hzero
  have read : burnolRadiusRestriction (1 / 4) value x = value x := hread
  rw [zero] at read
  exact read.symm.trans hzero

theorem burnolMobiusSourceL2_innerGap (value : BurnolPaAmbientCarrier) :
    (burnolMobiusSourceL2 value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  have sourceGap := burnolMobiusWindowSourceRead_innerGap value
  filter_upwards [ae_restrict_of_ae (burnolRadiusZeroExtension_coe
      (burnolMobiusWindowSourceRead value)), sourceGap] with x hext hgap
  change burnolMobiusSourceL2 value x =
    (symmetricInterval (4 : ℝ)).indicator (fun t => burnolMobiusWindowSourceRead value t) x at hext
  rw [hext]
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [Set.indicator_of_mem inside]
    exact hgap
  · rw [Set.indicator_of_notMem inside]

theorem burnolCompleteRemainderSource_innerGap (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (source : burnolCompactAnnulusSource) (order : Nat) :
    (burnolCompleteRemainderSource z source order : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  induction order with
  | zero =>
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (2 : ℂ)
          (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source))),
        burnolMobiusSourceL2_innerGap (burnolCompactAdditivePhysicalState source)]
          with x hsmul hgap
      change ((2 : ℂ) • burnolMobiusSourceL2
        (burnolCompactAdditivePhysicalState source) : BurnolL2) x = _
      rw [hsmul]
      change (2 : ℂ) * burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source) x = _
      rw [hgap, mul_zero]
  | succ order previous =>
      exact gap_of_restriction_zero _
        (burnolDirectRightResolvent_innerGap z rightQuarter _ previous)

theorem burnolPaResidualCompleteSource_innerGap {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    (burnolPaResidualCompleteSource observation nontrivial : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  let complete := burnolCompleteRemainderSource (observation.coordinate / 2)
    (burnolAnalyticComplementNormalizedSource observation)
    (generatedRiemannXiZeroOrder owner observation.coordinate)
  let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
    (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)
  have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub complete (burnolMobiusSourceL2 projection)),
    burnolCompleteRemainderSource_innerGap (observation.coordinate / 2) rightQuarter
      (burnolAnalyticComplementNormalizedSource observation)
      (generatedRiemannXiZeroOrder owner observation.coordinate),
    burnolMobiusSourceL2_innerGap projection] with x hsub hcomplete hprojection
  change (complete - burnolMobiusSourceL2 projection : BurnolL2) x = _
  rw [hsub]
  change complete x - burnolMobiusSourceL2 projection x = _
  rw [show complete x = 0 from hcomplete, hprojection, sub_self]

theorem burnolMobiusSourceL2_even (value : BurnolPaAmbientCarrier) :
    reflectL2 (burnolMobiusSourceL2 value) = burnolMobiusSourceL2 value := by
  let raw := burnolEvenStrongRepresentative (value : BurnolL2)
  let full : ℝ → ℂ := (symmetricInterval (4 : ℝ)).indicator (fun x =>
    ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
      ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) *
        (raw (x / (m : ℕ)) - burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value))
  have rawEven (x : ℝ) : raw (-x) = raw x := by
    unfold raw burnolEvenStrongRepresentative
    simp only [neg_neg, add_comm]
  have fullEven (x : ℝ) : full (-x) = full x := by
    classical
    have same : -x ∈ symmetricInterval (4 : ℝ) ↔ x ∈ symmetricInterval (4 : ℝ) := by
      simp only [symmetricInterval, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [full, indicator_apply, same]
    split_ifs
    · apply Finset.sum_congr rfl
      intro m _
      rw [neg_div, rawEven]
    · rfl
  have rawRep := burnolEvenStrongRepresentative_ae_eq (value : BurnolL2)
    (mem_evenL2ClosedFace_iff.mp value.property.2)
  have pulled (m : ℕ+) : ∀ᵐ x : ℝ ∂volume, raw (x / (m : ℕ)) =
      (value : BurnolL2) (x / (m : ℕ)) := by
    have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := ((m : ℕ) : ℝ)⁻¹) (inv_ne_zero positive.ne')
    simpa only [smul_eq_mul, inv_mul_eq_div] using qmp.ae rawRep
  have window := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (burnolMobiusWindowSourceRead_coeFn value)
  have fullRep : (burnolMobiusSourceL2 value : ℝ → ℂ) =ᵐ[volume] full := by
    filter_upwards [burnolRadiusZeroExtension_coe (burnolMobiusWindowSourceRead value),
      window, ae_all_iff.mpr pulled] with x hext hwindow hpulled
    change burnolMobiusSourceL2 value x =
      (symmetricInterval (4 : ℝ)).indicator (fun t => burnolMobiusWindowSourceRead value t) x at hext
    rw [hext]
    unfold full
    by_cases inside : x ∈ symmetricInterval (4 : ℝ)
    · rw [indicator_of_mem inside, indicator_of_mem inside, hwindow inside]
      apply Finset.sum_congr rfl
      intro m _
      rw [hpulled m]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (burnolMobiusSourceL2 value) negMeasurePreserving,
    fullRep, negMeasurePreserving.quasiMeasurePreserving.ae fullRep] with x href hright hleft
  change reflectL2 (burnolMobiusSourceL2 value) x = burnolMobiusSourceL2 value (-x) at href
  rw [href, hright, hleft, fullEven]

theorem burnolCompleteRemainderSource_even (z : ℂ)
    (source : burnolCompactAnnulusSource) (order : ℕ) :
    reflectL2 (burnolCompleteRemainderSource z source order) =
      burnolCompleteRemainderSource z source order := by
  induction order with
  | zero =>
      change reflectL2 ((2 : ℂ) • burnolMobiusSourceL2 _) = _
      rw [map_smul, burnolMobiusSourceL2_even]
      rfl
  | succ order previous =>
      change reflectL2 (burnolDirectRightResolvent z _) = burnolDirectRightResolvent z _
      unfold burnolDirectRightResolvent
      rw [map_neg, ← reflectL2.integral_comp_comm
        (burnolDirectRightResolventIntegrand z (burnolCompleteRemainderSource z source order))]
      congr 1
      apply integral_congr_ae
      filter_upwards with h
      dsimp only [burnolDirectRightResolventIntegrand]
      rw [map_smul, reflectL2_burnolMultiplicativeDilation, previous]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
