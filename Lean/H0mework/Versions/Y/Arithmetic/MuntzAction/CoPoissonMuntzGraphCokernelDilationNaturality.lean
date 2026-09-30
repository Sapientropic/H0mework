import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzDilationActionLaws

/-!
# Positive multiplicative action on the Müntz graph cokernel

Dense source readback upgrades the normalized quotient dilation family to
strict identity and composition laws.  Hence every Müntz graph cokernel
carries an actual continuous representation of the positive scale group.
No isometry or current-zero statement enters the construction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open SourceGeneratedFunctionalGraphCokernel

noncomputable section

theorem coPoissonMuntzGraphCokernelDilationAction_strict_source
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    (coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf scale positive).toLinearMap.comp
        (coPoissonMuntzGraphSourceMap z positiveZ belowHalf) =
      (coPoissonMuntzGraphSourceMap z positiveZ belowHalf).comp
        (normalizedQuarterDilationTestAction z scale positive) := by
  apply LinearMap.ext
  intro value
  exact coPoissonMuntzGraphCokernelDilationAction_source
    z positiveZ belowHalf scale positive value

theorem coPoissonMuntzGraphCokernelDilationAction_one
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf 1 (by norm_num) =
      ContinuousLinearMap.id ℂ
        (CoPoissonMuntzGraphCokernel z positiveZ belowHalf) := by
  apply ContinuousLinearMap.ext
  intro quotient
  have functionsEqual :=
    (canonicalSourceMap_denseRange
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (coPoissonQuarterMellinConvergentMap
        z positiveZ belowHalf)).equalizer
      (coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf 1 (by norm_num)).continuous
      (ContinuousLinearMap.id ℂ
        (CoPoissonMuntzGraphCokernel z positiveZ belowHalf)).continuous (by
          funext value
          change coPoissonMuntzGraphCokernelDilationAction
              z positiveZ belowHalf 1 (by norm_num)
                (coPoissonMuntzGraphSourceMap
                  z positiveZ belowHalf value) =
            ContinuousLinearMap.id ℂ
              (CoPoissonMuntzGraphCokernel z positiveZ belowHalf)
                (coPoissonMuntzGraphSourceMap
                  z positiveZ belowHalf value)
          rw [coPoissonMuntzGraphCokernelDilationAction_source,
            normalizedQuarterDilationTestAction_one]
          rfl)
  exact congrFun functionsEqual quotient

theorem coPoissonMuntzGraphCokernelDilationAction_comp
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf first firstPositive).comp
        (coPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf second secondPositive) =
      coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
        (first * second) (mul_pos firstPositive secondPositive) := by
  apply ContinuousLinearMap.ext
  intro quotient
  have functionsEqual :=
    (canonicalSourceMap_denseRange
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (coPoissonQuarterMellinConvergentMap
        z positiveZ belowHalf)).equalizer
      ((coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf first firstPositive).comp
        (coPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf second secondPositive)).continuous
      (coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
        (first * second) (mul_pos firstPositive secondPositive)).continuous (by
          funext value
          change coPoissonMuntzGraphCokernelDilationAction
              z positiveZ belowHalf first firstPositive
                (coPoissonMuntzGraphCokernelDilationAction
                  z positiveZ belowHalf second secondPositive
                  (coPoissonMuntzGraphSourceMap
                    z positiveZ belowHalf value)) =
            coPoissonMuntzGraphCokernelDilationAction
              z positiveZ belowHalf (first * second)
                (mul_pos firstPositive secondPositive)
                (coPoissonMuntzGraphSourceMap
                  z positiveZ belowHalf value)
          rw [coPoissonMuntzGraphCokernelDilationAction_source,
            coPoissonMuntzGraphCokernelDilationAction_source,
            coPoissonMuntzGraphCokernelDilationAction_source]
          have sourceComp := LinearMap.congr_fun
            (normalizedQuarterDilationTestAction_comp
              z first second firstPositive secondPositive) value
          change normalizedQuarterDilationTestAction z first firstPositive
              (normalizedQuarterDilationTestAction
                z second secondPositive value) =
            normalizedQuarterDilationTestAction z (first * second)
              (mul_pos firstPositive secondPositive) value at sourceComp
          rw [sourceComp])
  exact congrFun functionsEqual quotient

def positiveUnitValue (scale : Units NNReal) : ℝ :=
  ((scale : NNReal) : ℝ)

theorem positiveUnitValue_pos (scale : Units NNReal) :
    0 < positiveUnitValue scale := by
  exact_mod_cast
    (show (0 : NNReal) < (scale : NNReal) from
      pos_iff_ne_zero.mpr scale.ne_zero)

@[simp] theorem positiveUnitValue_one :
    positiveUnitValue (1 : Units NNReal) = 1 := by
  simp [positiveUnitValue]

@[simp] theorem positiveUnitValue_mul (first second : Units NNReal) :
    positiveUnitValue (first * second) =
      positiveUnitValue first * positiveUnitValue second := by
  simp [positiveUnitValue]

theorem coPoissonMuntzGraphCokernelDilationAction_congr
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    {first second : ℝ} (equality : first = second)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf first firstPositive =
      coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf second secondPositive := by
  subst second
  rfl

/-- Actual continuous representation of the positive multiplicative scale
group on the generated relation quotient. -/
def coPoissonMuntzGraphCokernelPositiveDilationAction
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    Units NNReal →*
      (CoPoissonMuntzGraphCokernel z positiveZ belowHalf →L[ℂ]
        CoPoissonMuntzGraphCokernel z positiveZ belowHalf) where
  toFun scale := coPoissonMuntzGraphCokernelDilationAction
    z positiveZ belowHalf (positiveUnitValue scale)
      (positiveUnitValue_pos scale)
  map_one' := by
    have identity := coPoissonMuntzGraphCokernelDilationAction_one
      z positiveZ belowHalf
    change coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf (positiveUnitValue (1 : Units NNReal))
          (positiveUnitValue_pos 1) = 1
    have identity' : coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf (positiveUnitValue (1 : Units NNReal))
          (positiveUnitValue_pos 1) =
        ContinuousLinearMap.id ℂ
          (CoPoissonMuntzGraphCokernel z positiveZ belowHalf) := by
      simpa only [positiveUnitValue_one] using identity
    rw [identity']
    apply ContinuousLinearMap.ext
    intro value
    rfl
  map_mul' first second := by
    have composition := (coPoissonMuntzGraphCokernelDilationAction_comp
      z positiveZ belowHalf
      (positiveUnitValue first) (positiveUnitValue second)
      (positiveUnitValue_pos first) (positiveUnitValue_pos second)).symm
    change coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
        (positiveUnitValue (first * second))
          (positiveUnitValue_pos (first * second)) =
      (coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
        (positiveUnitValue first) (positiveUnitValue_pos first)).comp
        (coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
          (positiveUnitValue second) (positiveUnitValue_pos second))
    calc
      _ = coPoissonMuntzGraphCokernelDilationAction z positiveZ belowHalf
          (positiveUnitValue first * positiveUnitValue second)
          (mul_pos (positiveUnitValue_pos first)
            (positiveUnitValue_pos second)) :=
        coPoissonMuntzGraphCokernelDilationAction_congr
          z positiveZ belowHalf (positiveUnitValue_mul first second)
          (positiveUnitValue_pos (first * second))
          (mul_pos (positiveUnitValue_pos first)
            (positiveUnitValue_pos second))
      _ = _ := composition

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
