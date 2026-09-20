import H0mework.Physics.Actual.FieldsCompactL2
import H0mework.Physics.Actual.FieldsFaithful

/-! Continuous whole fields are recovered from their complete compact L² reads. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open MeasureTheory Set Metric

noncomputable section

theorem compactPullback_eqOn_of_compactRead_eq
    {left right : StageNineHolonomicConfiguration}
    (leftSmooth : left.Smooth) (rightSmooth : right.Smooth)
    (scale : ℕ) (coordinate : Coordinate)
    (same : compactRead left leftSmooth scale coordinate =
      compactRead right rightSmooth scale coordinate) :
    EqOn (compactPullback left scale coordinate)
      (compactPullback right scale coordinate) unitCompact := by
  have leftRead := compactRead_coe_ae left leftSmooth scale coordinate
  rw [same] at leftRead
  have aeSame := leftRead.symm.trans (compactRead_coe_ae right rightSmooth scale coordinate)
  apply Measure.eqOn_of_ae_eq aeSame
    (compactPullback_continuous leftSmooth scale coordinate).continuousOn
    (compactPullback_continuous rightSmooth scale coordinate).continuousOn
  change closedBall (0 : BasePoint) 1 ⊆ closure (interior (closedBall (0 : BasePoint) 1))
  rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]

theorem exists_scale_pullback_point (point : BasePoint) :
    ∃ scale : ℕ, ∃ localPoint ∈ unitCompact, scaleRadius scale • localPoint = point := by
  obtain ⟨scale, scaleLarge⟩ := exists_nat_gt ‖point‖
  have radiusPositive := scaleRadius_pos scale
  have radiusLarge : ‖point‖ < scaleRadius scale := by
    unfold scaleRadius
    linarith
  refine ⟨scale, (scaleRadius scale)⁻¹ • point, ?_, ?_⟩
  · change dist ((scaleRadius scale)⁻¹ • point) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr radiusPositive)]
    exact le_of_lt ((inv_mul_lt_iff₀ radiusPositive).2 (by simpa using radiusLarge))
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt radiusPositive), one_smul]

theorem configuration_eq_of_compactRead_eq
    {left right : StageNineHolonomicConfiguration}
    (leftSmooth : left.Smooth) (rightSmooth : right.Smooth)
    (same : ∀ scale coordinate,
      compactRead left leftSmooth scale coordinate =
        compactRead right rightSmooth scale coordinate) : left = right := by
  apply configuration_eq_of_realCoordinate_eq
  intro coordinate point
  obtain ⟨scale, localPoint, localMem, recovers⟩ := exists_scale_pullback_point point
  have localEquality := compactPullback_eqOn_of_compactRead_eq
    leftSmooth rightSmooth scale coordinate (same scale coordinate) localMem
  simpa only [compactPullback, recovers] using localEquality

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
