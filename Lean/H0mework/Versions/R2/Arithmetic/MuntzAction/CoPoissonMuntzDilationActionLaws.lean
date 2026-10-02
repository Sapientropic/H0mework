import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernelDilationAction

/-!
# Multiplicative laws of the Müntz dilation actions

Raw and character-normalized dilation actions on the quarter-Mellin test and
Schwartz relation carriers obey strict identity and composition laws at all
positive scales.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open ClozelEndpointSourceEffect
open scoped SchwartzMap

noncomputable section

theorem quarterDilationCharacter_one (z : ℂ) :
    quarterDilationCharacter z 1 = 1 := by
  simp [quarterDilationCharacter]

theorem quarterDilationCharacter_mul
    (z : ℂ) (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    quarterDilationCharacter z (first * second) =
      quarterDilationCharacter z first *
        quarterDilationCharacter z second := by
  unfold quarterDilationCharacter
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg firstPositive.le secondPositive.le]

theorem quarterDilationWeight_one :
    positiveMellinQuarterDilationWeight 1 = 1 := by
  simp [positiveMellinQuarterDilationWeight]

theorem quarterDilationWeight_mul
    (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    positiveMellinQuarterDilationWeight (first * second) =
      positiveMellinQuarterDilationWeight first *
        positiveMellinQuarterDilationWeight second := by
  rw [quarterDilationWeight_eq_cpow_quarter
      (first * second) (mul_pos firstPositive secondPositive),
    quarterDilationWeight_eq_cpow_quarter first firstPositive,
    quarterDilationWeight_eq_cpow_quarter second secondPositive,
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg firstPositive.le secondPositive.le]

theorem quarterDilationTestAction_one (z : ℂ) :
    quarterDilationTestAction z 1 (by norm_num) = LinearMap.id := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext t
  change positiveMellinQuarterDilationWeight 1 *
      value.1 ⟨1 * t.1, mul_pos (by norm_num) t.2⟩ = value.1 t
  rw [quarterDilationWeight_one]
  simp

theorem quarterDilationTestAction_comp
    (z : ℂ) (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (quarterDilationTestAction z first firstPositive).comp
        (quarterDilationTestAction z second secondPositive) =
      quarterDilationTestAction z (first * second)
        (mul_pos firstPositive secondPositive) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext t
  change positiveMellinQuarterDilationWeight first *
      (positiveMellinQuarterDilationWeight second *
        value.1 ⟨second * (first * t.1),
          mul_pos secondPositive (mul_pos firstPositive t.2)⟩) =
    positiveMellinQuarterDilationWeight (first * second) *
      value.1 ⟨(first * second) * t.1,
        mul_pos (mul_pos firstPositive secondPositive) t.2⟩
  rw [quarterDilationWeight_mul first second firstPositive secondPositive]
  have inputEq :
      (⟨second * (first * t.1),
        mul_pos secondPositive (mul_pos firstPositive t.2)⟩ :
          PositiveMellinReal) =
        ⟨(first * second) * t.1,
          mul_pos (mul_pos firstPositive secondPositive) t.2⟩ := by
    apply Subtype.ext
    ring
  rw [inputEq]
  ring

theorem quarterMuntzSchwartzDilationAction_one :
    quarterMuntzSchwartzDilationAction 1 (by norm_num) = LinearMap.id := by
  apply LinearMap.ext
  intro test
  apply SchwartzMap.ext
  intro x
  change positiveMellinQuarterDilationWeight 1 *
      test (Real.sqrt 1 * x) = test x
  rw [quarterDilationWeight_one]
  norm_num

theorem quarterMuntzSchwartzDilationAction_comp
    (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (quarterMuntzSchwartzDilationAction first firstPositive).comp
        (quarterMuntzSchwartzDilationAction second secondPositive) =
      quarterMuntzSchwartzDilationAction (first * second)
        (mul_pos firstPositive secondPositive) := by
  apply LinearMap.ext
  intro test
  apply SchwartzMap.ext
  intro x
  change positiveMellinQuarterDilationWeight first *
      (positiveMellinQuarterDilationWeight second *
        test (Real.sqrt second * (Real.sqrt first * x))) =
    positiveMellinQuarterDilationWeight (first * second) *
      test (Real.sqrt (first * second) * x)
  rw [quarterDilationWeight_mul first second firstPositive secondPositive,
    Real.sqrt_mul firstPositive.le]
  have argumentEq :
      Real.sqrt second * (Real.sqrt first * x) =
        (Real.sqrt first * Real.sqrt second) * x := by ring
  rw [argumentEq]
  ring

theorem normalizedQuarterDilationTestAction_one (z : ℂ) :
    normalizedQuarterDilationTestAction z 1 (by norm_num) =
      LinearMap.id := by
  unfold normalizedQuarterDilationTestAction
  rw [quarterDilationCharacter_one, inv_one, one_smul,
    quarterDilationTestAction_one]

theorem normalizedQuarterDilationTestAction_comp
    (z : ℂ) (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (normalizedQuarterDilationTestAction z first firstPositive).comp
        (normalizedQuarterDilationTestAction z second secondPositive) =
      normalizedQuarterDilationTestAction z (first * second)
        (mul_pos firstPositive secondPositive) := by
  apply LinearMap.ext
  intro value
  change (quarterDilationCharacter z first)⁻¹ •
      quarterDilationTestAction z first firstPositive
        ((quarterDilationCharacter z second)⁻¹ •
          quarterDilationTestAction z second secondPositive value) =
    (quarterDilationCharacter z (first * second))⁻¹ •
      quarterDilationTestAction z (first * second)
        (mul_pos firstPositive secondPositive) value
  rw [map_smul]
  have rawComp := LinearMap.congr_fun
    (quarterDilationTestAction_comp
      z first second firstPositive secondPositive) value
  change quarterDilationTestAction z first firstPositive
      (quarterDilationTestAction z second secondPositive value) =
    quarterDilationTestAction z (first * second)
      (mul_pos firstPositive secondPositive) value at rawComp
  rw [rawComp, quarterDilationCharacter_mul
    z first second firstPositive secondPositive, smul_smul]
  congr 1
  field_simp [quarterDilationCharacter_ne_zero z first firstPositive,
    quarterDilationCharacter_ne_zero z second secondPositive]

theorem normalizedQuarterMuntzSchwartzDilationAction_one (z : ℂ) :
    normalizedQuarterMuntzSchwartzDilationAction z 1 (by norm_num) =
      LinearMap.id := by
  unfold normalizedQuarterMuntzSchwartzDilationAction
  rw [quarterDilationCharacter_one, inv_one, one_smul,
    quarterMuntzSchwartzDilationAction_one]

theorem normalizedQuarterMuntzSchwartzDilationAction_comp
    (z : ℂ) (first second : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (normalizedQuarterMuntzSchwartzDilationAction
        z first firstPositive).comp
        (normalizedQuarterMuntzSchwartzDilationAction
          z second secondPositive) =
      normalizedQuarterMuntzSchwartzDilationAction
        z (first * second) (mul_pos firstPositive secondPositive) := by
  apply LinearMap.ext
  intro test
  change (quarterDilationCharacter z first)⁻¹ •
      quarterMuntzSchwartzDilationAction first firstPositive
        ((quarterDilationCharacter z second)⁻¹ •
          quarterMuntzSchwartzDilationAction second secondPositive test) =
    (quarterDilationCharacter z (first * second))⁻¹ •
      quarterMuntzSchwartzDilationAction (first * second)
        (mul_pos firstPositive secondPositive) test
  rw [map_smul]
  have rawComp := LinearMap.congr_fun
    (quarterMuntzSchwartzDilationAction_comp
      first second firstPositive secondPositive) test
  change quarterMuntzSchwartzDilationAction first firstPositive
      (quarterMuntzSchwartzDilationAction second secondPositive test) =
    quarterMuntzSchwartzDilationAction (first * second)
      (mul_pos firstPositive secondPositive) test at rawComp
  rw [rawComp, quarterDilationCharacter_mul
    z first second firstPositive secondPositive, smul_smul]
  congr 1
  field_simp [quarterDilationCharacter_ne_zero z first firstPositive,
    quarterDilationCharacter_ne_zero z second secondPositive]

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
