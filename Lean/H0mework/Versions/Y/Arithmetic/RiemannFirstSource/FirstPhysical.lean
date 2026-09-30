import H0mework.Versions.Y.Arithmetic.RiemannResolvent.CompleteGap
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.UnitTail
import H0mework.Versions.Y.Arithmetic.RemainderSource.Recovery

/-! The original zero occurrence generates an occupied first Pa-complement state; no simplicity premise. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

local instance firstPhysicalAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolAnalyticComplementFirstPhysicalState {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial 1,
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf 1
      (generatedRiemannXiZeroOrder_pos observation nontrivial)⟩

private theorem l2_star_sub (left right : BurnolL2) :
    star (left - right) = star left - star right := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (left - right), Lp.coeFn_sub left right,
    Lp.coeFn_sub (star left) (star right), Lp.coeFn_star left, Lp.coeFn_star right]
      with x hleft hsub hright hstarLeft hstarRight
  simp only [Pi.star_apply, Pi.sub_apply] at hleft hsub hright hstarLeft hstarRight
  rw [hleft, hsub, _root_.star_sub, hright, hstarLeft, hstarRight]

theorem burnolAnalyticComplementFirstPhysicalState_notInPa {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf ∉ burnolCompactCoPoissonClosedRange := by
  intro inPa
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let state := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
  let source := burnolCompleteRemainderSource (observation.coordinate / 2)
    (burnolAnalyticComplementNormalizedSource observation) 1
  have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  have same : source - burnolMobiusSourceL2 state = 0 := by
    apply burnolRemainderSourceRead_faithful
    · rw [map_sub, burnolCompleteRemainderSource_even, burnolMobiusSourceL2_even]
    · filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub source (burnolMobiusSourceL2 state)),
        burnolCompleteRemainderSource_innerGap _ rightQuarter
          (burnolAnalyticComplementNormalizedSource observation) 1,
        burnolMobiusSourceL2_innerGap state] with x hsub hsource hpa
      rw [hsub]
      change source x - burnolMobiusSourceL2 state x = _
      rw [hsource, hpa, sub_self]
    · intro test
      have full := burnolCompleteRemainderSource_realizes (observation.coordinate / 2)
        rightQuarter (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (burnolAnalyticComplementNormalizedSource observation) 1 test
      have projected := burnolRemainderSourceRead_Pa state inPa test
      have realized : burnolRemainderSourceRead source test = ∫ x : ℝ, test x * (state : BurnolL2) x := by
        simpa only [source, state, burnolAnalyticComplementFirstPhysicalState,
          burnolAnalyticComplementDivisionAdditiveState, burnolAnalyticComplementDivisionState,
          burnolAnalyticComplementCompletionSource,
          Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using full
      change (1 / 2 : ℂ) * inner ℂ (star (source - burnolMobiusSourceL2 state))
        (burnolRemainderL2Kernel test) = 0
      rw [l2_star_sub, inner_sub_left, mul_sub]
      change burnolRemainderSourceRead source test -
        burnolRemainderSourceRead (burnolMobiusSourceL2 state) test = 0
      rw [realized, projected, sub_self]
  exact burnolCompleteFirstSource_ne_mobiusSource coordinate state (sub_eq_zero.mp same)

theorem burnolAnalyticComplementFirstPaResidual_nonzero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) ≠ 0 := by
  intro zero
  apply burnolAnalyticComplementFirstPhysicalState_notInPa observation nontrivial rightHalf
  change burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf ∈
    burnolCompactCoPoissonClosedRange.toSubmodule
  simpa only [Submodule.orthogonal_orthogonal] using
    (Submodule.starProjection_apply_eq_zero_iff _).mp zero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
