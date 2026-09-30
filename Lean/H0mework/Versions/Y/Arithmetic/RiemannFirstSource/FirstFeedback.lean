import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.FirstSourceSplit

/-! The canonical source split reads back the same original Pa residual on every Schwartz test. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

local instance canonicalSource3AmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem remainderRead_sub (left right : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (left - right) test =
      burnolRemainderSourceRead left test - burnolRemainderSourceRead right test := by
  have kernelMem : MemLp (fun x : ℝ => coPoissonMuntzScaleRemainder test |x|) 2 volume :=
    (Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)
  rw [burnolRemainderSourceRead_integral, burnolRemainderSourceRead_integral,
    burnolRemainderSourceRead_integral, ← mul_sub,
    ← integral_sub (f := fun x : ℝ => left x * coPoissonMuntzScaleRemainder test |x|)
      (g := fun x : ℝ => right x * coPoissonMuntzScaleRemainder test |x|)
      ((Lp.memLp left).integrable_mul kernelMem)
      ((Lp.memLp right).integrable_mul kernelMem)]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub left right] with x hsub
  rw [hsub]
  change (left x - right x) * _ = _
  ring

theorem burnolAnalyticComplementFirstPaSource_readback {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (test : SchwartzMap ℝ ℂ) :
    let value := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
    let residue := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection value
    burnolRemainderSourceRead (burnolMobiusSourceL2 residue +
        burnolNormalizedFirstSourceUnitTail (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)) test =
      ∫ x : ℝ, test x * (residue : BurnolL2) x := by
  dsimp only
  rw [← burnolAnalyticComplementFirstPaSource_split observation nontrivial rightHalf, remainderRead_sub]
  let value := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
  let projected := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection value
  have rightQuarter : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  have full := burnolCompleteRemainderSource_realizes (observation.coordinate / 2)
    rightQuarter (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (burnolAnalyticComplementNormalizedSource observation) 1 test
  have valueRead : burnolRemainderSourceRead
      (burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation) 1) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (value : BurnolL2)) test := by
    simpa only [value, burnolAnalyticComplementFirstPhysicalState,
      burnolAnalyticComplementDivisionAdditiveState, burnolAnalyticComplementDivisionState,
      burnolAnalyticComplementCompletionSource] using full
  have projectionRead : burnolRemainderSourceRead (burnolMobiusSourceL2 projected) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (projected : BurnolL2)) test := by
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
    exact burnolRemainderSourceRead_Pa projected (Submodule.starProjection_apply_mem _ _) test
  change burnolRemainderSourceRead _ test - burnolRemainderSourceRead (burnolMobiusSourceL2 projected) test = _
  rw [valueRead, projectionRead, ← sub_apply, ← map_sub]
  rw [Submodule.starProjection_orthogonal_val]
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
