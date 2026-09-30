import Mathlib.Analysis.Complex.Basic

/-!
# Log-position and translation cone

On raw complex-valued functions, translation and multiplication by the
coordinate have an exact commutator.  This is the unbounded operator law
before any Hilbert completion; no boundedness or domain premise is hidden.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace GenericFoundation
namespace Analysis
namespace LogPositionTranslationCone

noncomputable section

abbrev RawLogState := ℝ → ℂ

def rawLogTranslate (shift : ℝ) (state : RawLogState) : RawLogState :=
  fun x => state (x + shift)

def rawLogPosition (state : RawLogState) : RawLogState :=
  fun x => (x : ℂ) * state x

theorem translate_position_sub_position_translate
    (shift : ℝ) (state : RawLogState) :
    rawLogTranslate shift (rawLogPosition state) -
        rawLogPosition (rawLogTranslate shift state) =
      fun x => (shift : ℂ) * rawLogTranslate shift state x := by
  funext x
  simp [rawLogTranslate, rawLogPosition]
  ring

theorem translate_position_sub_position_translate_apply
    (shift : ℝ) (state : RawLogState) (x : ℝ) :
    rawLogTranslate shift (rawLogPosition state) x -
        rawLogPosition (rawLogTranslate shift state) x =
      (shift : ℂ) * rawLogTranslate shift state x := by
  exact congrFun
    (translate_position_sub_position_translate shift state) x

end
end LogPositionTranslationCone
end Analysis
end GenericFoundation
end SaturationMonoid
