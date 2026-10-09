import H0mework.Versions.V2.Arithmetic.RieszSynthesis.GapMean
import H0mework.Versions.V2.Arithmetic.MobiusSource.Tate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory
open scoped ArithmeticFunction BigOperators InnerProductSpace
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem ambient_inner_smul (coefficient : ℂ) (left right : BurnolPaAmbientCarrier) :
    inner ℂ (coefficient • left) right = star coefficient * inner ℂ left right := by
  simpa only [starRingEnd_apply] using (inner_smul_left (𝕜 := ℂ) left right coefficient)

private def windowPullbackAdjoint (m : ℕ+) : BurnolRadiusIntervalL2 4 →L[ℂ] BurnolPaAmbientCarrier :=
  (Real.exp (Real.log (m : ℕ) / 2) : ℂ) •
      burnolEvenAmbientProjection.comp
        ((burnolMultiplicativeDilation (Real.log (m : ℕ))).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (burnolRadiusZeroExtension 4)) -
    gapMeanAdjoint.comp (innerSL ℂ (intervalConstant 4))

private theorem windowPullbackAdjoint_read (m : ℕ+)
    (window : BurnolRadiusIntervalL2 4) (value : BurnolPaAmbientCarrier) :
    inner ℂ (windowPullbackAdjoint m window) value =
      inner ℂ window (burnolMobiusWindowPullback m value) := by
  let weight : ℂ := Real.exp (Real.log (m : ℕ) / 2)
  have mainRead :
      inner ℂ (burnolEvenAmbientProjection
        (burnolMultiplicativeDilation (Real.log (m : ℕ))
          (burnolRadiusZeroExtension 4 window))) value =
      inner ℂ window (burnolRadiusRestriction 4
        (burnolMultiplicativeDilation (-Real.log (m : ℕ)) (value : BurnolL2))) := by
    calc
      _ = inner ℂ (burnolMultiplicativeDilation (Real.log (m : ℕ))
          (burnolRadiusZeroExtension 4 window)) (value : BurnolL2) :=
        (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
          |>.inner_orthogonalProjectionOnto_eq_of_mem_right value _
      _ = inner ℂ (burnolRadiusZeroExtension 4 window)
          (burnolMultiplicativeDilation (-Real.log (m : ℕ)) (value : BurnolL2)) := by
        rw [(burnolMultiplicativeDilation (Real.log (m : ℕ))).inner_map_eq_flip,
          ← burnolMultiplicativeDilation_neg_eq_symm]
      _ = _ := (burnolRadiusRestriction 4).adjoint_inner_left _ window
  change inner ℂ
      (weight • burnolEvenAmbientProjection
          (burnolMultiplicativeDilation (Real.log (m : ℕ)) (burnolRadiusZeroExtension 4 window)) -
        gapMeanAdjoint (inner ℂ (intervalConstant 4) window)) value =
      inner ℂ window (weight • burnolRadiusRestriction 4
          (burnolMultiplicativeDilation (-Real.log (m : ℕ)) (value : BurnolL2)) -
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value • intervalConstant 4)
  rw [inner_sub_left, ambient_inner_smul, mainRead, inner_sub_right, inner_smul_right,
    gapMeanAdjoint_eq, ContinuousLinearMap.adjoint_inner_left]
  have realWeight : star weight = weight := Complex.conj_ofReal _
  have reverseInner : star (inner ℂ (intervalConstant 4) window) =
      inner ℂ window (intervalConstant 4) := inner_conj_symm _ _
  simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [realWeight, reverseInner, inner_smul_right]

/-- The original positive-divisor inventory is reversed term by term, with its gap subtraction retained. -/
def mobiusAdjoint : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
  (∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
    star ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) •
      windowPullbackAdjoint m).comp (burnolRadiusRestriction 4)

theorem mobiusAdjoint_eq : mobiusAdjoint = burnolMobiusSourceL2.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro source value
  have restrictionRead := (burnolRadiusRestriction 4).adjoint_inner_right source
    (burnolMobiusWindowSourceRead value)
  change inner ℂ source (burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)) =
    inner ℂ (burnolRadiusRestriction 4 source) (burnolMobiusWindowSourceRead value) at restrictionRead
  change inner ℂ (mobiusAdjoint source) value =
    inner ℂ source (burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value))
  rw [restrictionRead]
  simp only [mobiusAdjoint, ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    sum_inner, ambient_inner_smul, star_star, windowPullbackAdjoint_read,
    burnolMobiusWindowSourceRead, inner_sum, inner_smul_right]

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
