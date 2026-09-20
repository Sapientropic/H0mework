import H0mework.Physics.Geometry.CompactSupportIntegrationByParts

namespace SaturationMonoid.PhysicsCore.StageNineFundamentalLemma

open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open MeasureTheory
open scoped ContDiff

noncomputable section

theorem exists_compactSmoothVariation_integral_pos_of_continuous_pos_at
    (coefficient : BasePoint → ℝ) (coefficientContinuous : Continuous coefficient)
    (point : BasePoint) (coefficientPositive : 0 < coefficient point) :
    ∃ variation : CompactlySupportedSmoothVariation ℝ,
      0 < ∫ candidate : BasePoint, variation candidate * coefficient candidate := by
  have positiveOpen : IsOpen {candidate | 0 < coefficient candidate} :=
    isOpen_lt continuous_const coefficientContinuous
  obtain ⟨radius, radiusPositive, ballSubset⟩ :=
    (Metric.isOpen_iff.mp positiveOpen) point coefficientPositive
  let bump : ContDiffBump point :=
    { rIn := radius / 2
      rOut := radius
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let variation : CompactlySupportedSmoothVariation ℝ :=
    { toFun := bump
      smooth := bump.contDiff
      compactSupport := bump.hasCompactSupport }
  refine ⟨variation, ?_⟩
  have productContinuous : Continuous fun candidate : BasePoint =>
      variation candidate * coefficient candidate :=
    variation.smooth.continuous.mul coefficientContinuous
  have productCompact : HasCompactSupport fun candidate : BasePoint =>
      variation candidate * coefficient candidate :=
    variation.compactSupport.mul_right
  have productNonnegative : 0 ≤ fun candidate : BasePoint =>
      variation candidate * coefficient candidate := by
    intro candidate
    by_cases candidateSupport : candidate ∈ Function.support bump
    · have candidateBall : candidate ∈ Metric.ball point radius := by
        simpa [bump, ContDiffBump.support_eq] using candidateSupport
      exact mul_nonneg bump.nonneg (ballSubset candidateBall).le
    · have bumpZero : bump candidate = 0 := by
        simpa only [Function.mem_support, not_not] using candidateSupport
      simp [variation, bumpZero]
  have productPointNonzero :
      variation point * coefficient point ≠ 0 := by
    have bumpOne : bump point = 1 := by
      apply bump.one_of_mem_closedBall
      exact Metric.mem_closedBall_self bump.rIn_pos.le
    simp [variation, bumpOne, coefficientPositive.ne']
  exact productContinuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    productCompact productNonnegative productPointNonzero

theorem continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (coefficient : BasePoint → ℝ) (coefficientContinuous : Continuous coefficient)
    (stationary : ∀ variation : CompactlySupportedSmoothVariation ℝ,
      (∫ point : BasePoint, variation point * coefficient point) = 0) :
    coefficient = 0 := by
  funext point
  by_contra coefficientNonzero
  rcases lt_or_gt_of_ne coefficientNonzero with coefficientNegative | coefficientPositive
  · obtain ⟨variation, variationPositive⟩ :=
      exists_compactSmoothVariation_integral_pos_of_continuous_pos_at
        (-coefficient) coefficientContinuous.neg point (neg_pos.mpr coefficientNegative)
    have variationZero := stationary variation
    have negVariationZero :
        (∫ candidate : BasePoint,
          variation candidate * (-coefficient) candidate) = 0 := by
      rw [show (fun candidate : BasePoint =>
          variation candidate * (-coefficient) candidate) =
          fun candidate => -(variation candidate * coefficient candidate) by
        funext candidate
        simp]
      rw [integral_neg, variationZero, neg_zero]
    exact (ne_of_gt variationPositive) negVariationZero
  · obtain ⟨variation, variationPositive⟩ :=
      exists_compactSmoothVariation_integral_pos_of_continuous_pos_at
        coefficient coefficientContinuous point coefficientPositive
    exact (ne_of_gt variationPositive) (stationary variation)

end

end SaturationMonoid.PhysicsCore.StageNineFundamentalLemma
