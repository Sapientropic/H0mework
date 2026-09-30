import H0mework.Arithmetic.Mellin.MellinDilationAction
import H0mework.Arithmetic.Mellin.Functional

/-!
# Positive-domain Mellin carrier

Mellin functions are restricted to the literal domain `Ioi 0`; extension by
zero retains Mathlib's Mellin API.  The carrier receives the earlier
whole-line convergent submodule by canonical restriction, and positive
dilation acts with the exact Mellin character `a⁻ᶻ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set

noncomputable section

def restrictPositiveMellin (z : ℂ) :
    mellinConvergentSubmodule z →ₗ[ℂ]
      positiveMellinConvergentSubmodule z where
  toFun f :=
    ⟨fun t => f.1 t.1, by
      change MellinConvergent
        (positiveMellinExtension (fun t => f.1 t.1)) z
      have source := f.2
      unfold MellinConvergent at source ⊢
      apply source.congr_fun
      · intro t ht
        change 0 < t at ht
        simp [positiveMellinExtension, ht]
      · exact measurableSet_Ioi⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem positiveMellinFunctional_restrictPositive
    (z : ℂ) (f : mellinConvergentSubmodule z) :
    positiveMellinFunctional z (restrictPositiveMellin z f) =
      mellinFunctional z f := by
  unfold positiveMellinFunctional mellinFunctional mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  simp [positiveMellinExtension, restrictPositiveMellin, ht]

def positiveMellinDilation
    (z : ℂ) (a : ℝ) (positive : 0 < a) :
    positiveMellinConvergentSubmodule z →ₗ[ℂ]
      positiveMellinConvergentSubmodule z where
  toFun f :=
    ⟨fun t => f.1 ⟨a * t.1, mul_pos positive t.2⟩, by
      change MellinConvergent
        (positiveMellinExtension
          (fun t => f.1 ⟨a * t.1, mul_pos positive t.2⟩)) z
      have scaled :=
        (MellinConvergent.comp_mul_left positive).2 f.2
      unfold MellinConvergent at scaled ⊢
      apply scaled.congr_fun
      · intro t ht
        change 0 < t at ht
        simp [positiveMellinExtension, ht, mul_pos positive ht]
      · exact measurableSet_Ioi⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem positiveMellinFunctional_dilation
    (z : ℂ) (a : ℝ) (positive : 0 < a)
    (f : positiveMellinConvergentSubmodule z) :
    positiveMellinFunctional z
        (positiveMellinDilation z a positive f) =
      (a : ℂ) ^ (-z) • positiveMellinFunctional z f := by
  have source := mellin_comp_mul_left
    (positiveMellinExtension f.1) z positive
  change mellin
      (positiveMellinExtension
        (positiveMellinDilation z a positive f).1) z = _
  rw [show positiveMellinExtension
      (positiveMellinDilation z a positive f).1 =
      (fun t => positiveMellinExtension f.1 (a * t)) by
    funext t
    by_cases ht : 0 < t
    · simp [positiveMellinExtension, positiveMellinDilation,
        ht, mul_pos positive ht]
    · have notScaled : ¬ 0 < a * t := by
        exact not_lt.mpr <| mul_nonpos_of_nonneg_of_nonpos
          positive.le (le_of_not_gt ht)
      simp [positiveMellinExtension, positiveMellinDilation,
        ht, notScaled]]
  exact source

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
