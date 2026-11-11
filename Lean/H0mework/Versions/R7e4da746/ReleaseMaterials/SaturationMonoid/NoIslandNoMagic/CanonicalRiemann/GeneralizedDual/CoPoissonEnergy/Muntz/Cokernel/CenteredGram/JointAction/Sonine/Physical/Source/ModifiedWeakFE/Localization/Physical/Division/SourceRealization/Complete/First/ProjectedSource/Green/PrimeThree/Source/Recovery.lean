import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Recovery
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderClosedRange
import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.CompleteGap

/-! The original Pa source generates its faithful representative and its physical constant, without choosing a new source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem primeThreePa_source_representative (p : BurnolPaAmbientCarrier)
    (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    ∃ raw : ℝ → ℂ, (burnolMobiusSourceL2 p : ℝ → ℂ) =ᵐ[volume] raw ∧
      (∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0) ∧
      (p : BurnolL2) =ᵐ[volume] (fun x => burnolInnerGapForward raw x +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p) := by
  obtain ⟨raw, represents, gap, original⟩ :=
    burnolRemainderSourceRead_realization_ae (burnolMobiusSourceL2 p) (p : BurnolL2)
      (burnolMobiusSourceL2_even p) (burnolMobiusSourceL2_innerGap p)
      (burnolRemainderSourceRead_Pa p inPa)
  let C := ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u
  have gapEquation : (-C) • intervalConstant burnolUnscaledCommonGapRadius =
      restrictToInterval burnolUnscaledCommonGapRadius (p : BurnolL2) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-C) (intervalConstant burnolUnscaledCommonGapRadius),
      intervalConstant_coeFn burnolUnscaledCommonGapRadius,
      LpToLpRestrictCLM_coeFn ℂ (symmetricInterval burnolUnscaledCommonGapRadius) (p : BurnolL2),
      ae_restrict_of_ae original,
      ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)]
      with x hsmul hconstant hrestrict hvalue inside
    have restriction : restrictToInterval burnolUnscaledCommonGapRadius (p : BurnolL2) x =
        (p : BurnolL2) x := hrestrict
    rw [hsmul]
    change (-C) * intervalConstant burnolUnscaledCommonGapRadius x = _
    rw [hconstant, mul_one, restriction, hvalue]
    have small : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr inside
    rw [burnolInnerGapForward_innerGap raw gap small, zero_sub]
  have mean := burnolConstantGapCoefficient_eq burnolUnscaledCommonGapRadius
    (by norm_num [burnolUnscaledCommonGapRadius]) p (-C) gapEquation
  refine ⟨raw, represents, gap, ?_⟩
  filter_upwards [original] with x hx
  rw [hx, mean]
  rfl

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
