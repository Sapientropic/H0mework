import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderClosedRange
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.OneSource

/-! The fixed exact-order occurrence directly consumes its comb-remainder source action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

local instance remainderActionAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The evolved source realizes the exact-order projection's actual
dilation. No shifted Pa membership or boundary cancellation is supplied. -/
theorem burnolExactOrderPaRemainderSource_dilation {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    let value := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)
    burnolRemainderSourceRead (burnolMultiplicativeDilation shift
        (burnolMobiusSourceL2 value)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation shift (value : BurnolL2))) test := by
  dsimp only
  simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] using burnolRemainderSourceRead_Pa_action shift _
      (Submodule.starProjection_apply_mem _ _) test

/-- The original paired projection's complete effect is computed from
the same comb source. Both native correction terms remain in the equation. -/
theorem burnolExactOrderPaPairedProjection_remainderSource {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) (nonnegative : 0 ≤ shift) (small : shift ≤ Real.log 2)
    (test : SchwartzMap ℝ ℂ) :
    let value := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)
    let source := burnolMobiusSourceL2 value
    (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolPairedAmbientCompression shift value : BurnolL2)) test =
      (1 / 2 : ℂ) *
        (burnolRemainderSourceRead (burnolMultiplicativeDilation shift source) test +
          burnolRemainderSourceRead (burnolMultiplicativeDilation (-shift) source) test) -
      (1 / 2 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolPaIntervalSourceCorrection shift source +
          fourierL2 (burnolPaIntervalSourceCorrection shift
            (burnolTateReciprocalL2 source)))) test := by
  dsimp only
  have actual := congrArg
    (fun value : BurnolL2 => (Lp.toTemperedDistributionCLM ℂ volume 2 value) test)
    (burnolExactOrderPaPairedProjection_oneSource observation nontrivial
      shift nonnegative small)
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at actual
  rw [actual]
  congr 1
  rw [burnolExactOrderPaRemainderSource_dilation observation nontrivial shift test,
    burnolExactOrderPaRemainderSource_dilation observation nontrivial (-shift) test]
  simp only [pairedBurnolMultiplicativeDilation, smul_apply, add_apply,
    map_smul, map_add, ContinuousLinearEquiv.coe_coe, smul_eq_mul]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
