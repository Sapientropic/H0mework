import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.ResolventSource
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Algebra
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseAction

/-! Different parameters of the same counting source generate nonzero resolvent differences and their actual strong dilation derivatives. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolUnitTailResponse_difference_resolvent
    (left right : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse left 1 - burnolUnitTailResponse right 1 =
      ((left.value - right.value) / 2) •
        burnolDirectRightResolvent (left.value / 2) (burnolUnitTailResponse right 1) := by
  have lRight : 1 / 4 < (left.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [left.rightHalf]
  have rRight : 1 / 4 < (right.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [right.rightHalf]
  have resolvent := burnolDirectRightResolvent_identity (left.value / 2) (right.value / 2)
    lRight rRight burnolUnitCountingPrimitiveL2
  have negMap (z : ℂ) (value : BurnolL2) :
      burnolDirectRightResolvent z (-value) = -burnolDirectRightResolvent z value := by
    simpa only [neg_one_smul] using burnolDirectRightResolvent_smul z (-1) value
  rw [burnolUnitTailResponse_one_eq_fixedResolvent left, burnolUnitTailResponse_one_eq_fixedResolvent right,
    burnolDirectRightResolvent_sub _ lRight, negMap, burnolDirectRightResolvent_smul,
    sub_eq_iff_eq_add.mp resolvent]
  module

/-- Cancellation of the common primitive produces strong-domain data; no derivative witness is supplied. -/
theorem burnolUnitTailResponse_difference_hasDerivAt
    (left right : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (burnolUnitTailResponse left 1 - burnolUnitTailResponse right 1))
      ((left.value / 2 - 1 / 4) • burnolUnitTailResponse left 1 -
        (right.value / 2 - 1 / 4) • burnolUnitTailResponse right 1) 0 := by
  have lRight : 1 / 4 < (left.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [left.rightHalf]
  have generated := (burnolDirectRightResolventOrbit_hasDerivAt (left.value / 2) lRight
    (burnolUnitTailResponse right 1)).const_smul ((left.value - right.value) / 2)
  convert! generated using 1
  · funext h
    rw [burnolUnitTailResponse_difference_resolvent, map_smul]
    rfl
  · have identity := burnolUnitTailResponse_difference_resolvent left right
    rw [sub_eq_iff_eq_add.mp identity]
    module

theorem burnolUnitTailResponse_one_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate 1 ≠ 0 := by
  have radius : 4 * Real.exp ((-2 * Real.log 4) / 2) = (1 : ℝ) := by
    rw [show (-2 * Real.log 4) / 2 = -Real.log 4 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have source := burnolUnitTailResponse_dilation coordinate (-2 * Real.log 4) (by rw [radius]; norm_num)
  rw [radius] at source
  intro zero
  rw [zero, smul_zero] at source
  apply burnolUnitTailResponse_nonzero coordinate
  exact (burnolMultiplicativeDilation (-(-2 * Real.log 4) / 2)).injective
    (source.trans (map_zero _).symm)

theorem burnolUnitTailResponse_difference_ne_zero
    (left right : BurnolCompletedMellinCoordinate) (distinct : left.value ≠ right.value) :
    burnolUnitTailResponse left 1 - burnolUnitTailResponse right 1 ≠ 0 := by
  rw [burnolUnitTailResponse_difference_resolvent]
  apply smul_ne_zero (div_ne_zero (sub_ne_zero.mpr distinct) (by norm_num))
  intro zero
  apply burnolUnitTailResponse_one_ne_zero right
  apply burnolDirectRightResolvent_reflects_zero (left.value / 2) _ _ zero
  rw [Complex.div_re]
  norm_num
  linarith [left.rightHalf]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
