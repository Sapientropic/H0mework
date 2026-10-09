import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementHeatJetContinuation
import H0mework.Versions.V2.Arithmetic.RemainderSource.Continuity

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Pricing
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Original normalized heat after the actual R, retaining its complete ambient residual. -/
theorem original_R_scalar_action (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (current : BurnolPaAmbientCarrier) (w : ℂ)
    (wRightQuarter : 1 / 4 < w.re) (wBelowHalf : w.re < 1 / 2) :
    let coordinate := burnolDivisionCompletedMellinCoordinate w wRightQuarter wBelowHalf
    let raw := burnolDirectRightResolvent z (current : BurnolL2)
    let next := burnolEvenAmbientProjection raw
    let residual := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection raw
    burnolDivisionNormalizedPhysicalHeatMellin next w +
      2 * burnolAmbientCompletedMellinEvaluator coordinate residual =
        (-(1 / (z + w - (1 / 2 : ℂ)))) *
          burnolDivisionNormalizedPhysicalHeatMellin current w := by
  intro coordinate raw next residual
  let read := burnolAmbientCompletedMellinEvaluator coordinate
  have decay : (((1 / 2 : ℂ) - z - w).re < 0) := by
    simp only [Complex.sub_re]
    norm_num
    linarith
  have rawAction : read raw = (-(1 / (z + w - (1 / 2 : ℂ)))) * read (current : BurnolL2) := by
    have integrable := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter (current : BurnolL2)
    have integralRead : read raw = -∫ h : ℝ in Ioi 0,
        positiveMellinQuarterRightResolventWeight z h * quarterDilationCharacter w (Real.exp h) *
          read (current : BurnolL2) := by
      change read (-∫ h : ℝ in Ioi 0,
        burnolDirectRightResolventIntegrand z (current : BurnolL2) h) = _
      rw [map_neg, ← read.integral_comp_comm integrable]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h positive
      change burnolAmbientCompletedMellinEvaluator coordinate
        (positiveMellinQuarterRightResolventWeight z h •
          burnolMultiplicativeDilation (-h / 2) (current : BurnolL2)) = _
      rw [map_smul, burnolAmbientCompletedMellinEvaluator_dilation_of_positionGap
        coordinate (-h / 2) (by change 0 < h at positive; linarith)
        (current : BurnolL2) current.property.1.1]
      change positiveMellinQuarterRightResolventWeight z h *
        (Complex.exp (((2 * w) - (1 / 2 : ℂ)) * ((-h / 2 : ℝ) : ℂ)) *
          read (current : BurnolL2)) = _
      rw [divisionJet_ambientDilationExp_eq_quarterCharacter]
      exact (mul_assoc _ _ _).symm
    rw [integralRead, integral_mul_const,
      positiveMellinQuarterRightResolvent_scalarKernel z w decay]
    exact (neg_mul (1 / (z + w - (1 / 2 : ℂ))) (read (current : BurnolL2))).symm
  have heatRead (value : BurnolPaAmbientCarrier) :
      burnolDivisionNormalizedPhysicalHeatMellin value w = 2 * read (value : BurnolL2) := by
    have bridge := burnolGenericHomogeneousGammaMellinBridge value coordinate
    have restriction := congrArg (fun functional : BurnolPaAmbientCarrier →L[ℂ] ℂ => functional value)
      (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
    change read (value : BurnolL2) = burnolCompletedMellinEvaluator coordinate value at restriction
    have gammaNe : Gammaℝ (2 * w) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.mul_re]
      norm_num
      linarith
    rw [burnolDivisionCompletedMellinCoordinate_value,
      show (2 * w) / 2 = w by ring] at bridge
    change Gammaℝ (2 * w) * burnolCompletedMellinEvaluator coordinate value =
      (1 / 2 : ℂ) * mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) w at bridge
    have heatEq : mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) w =
        2 * (Gammaℝ (2 * w) * burnolCompletedMellinEvaluator coordinate value) := by
      rw [bridge, ← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
    unfold burnolDivisionNormalizedPhysicalHeatMellin
    rw [restriction, heatEq, mul_left_comm (Gammaℝ (2 * w))⁻¹ 2,
      inv_mul_cancel_left₀ gammaNe]
  have complete : (next : BurnolL2) + residual = raw := by
    change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection raw +
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection raw = raw
    exact Submodule.starProjection_add_starProjection_orthogonal raw
  have scalarComplete := congrArg read complete
  rw [map_add] at scalarComplete
  rw [heatRead next, heatRead current]
  calc
    _ = 2 * (read (next : BurnolL2) + read residual) := (mul_add _ _ _).symm
    _ = 2 * read raw := congrArg ((2 : ℂ) * ·) scalarComplete
    _ = _ := by rw [rawAction]; exact mul_left_comm _ _ _

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Pricing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
