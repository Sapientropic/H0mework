import H0mework.Arithmetic.Mellin.QuarterEnergy

/-!
# Narrow character boundary for quarter energy

A nonzero bounded eigenfunctional of an isometric translation has a
unit-modulus character.  This source-neutral Hilbert fact is kept below all
q-rich, endpoint, zero, and radial consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory

noncomputable section

abbrev PositiveMellinQuarterEnergyCharacterDomain :=
  PositiveMellinQuarterEnergy

theorem positiveMellinQuarterEnergy_character_norm_eq_one
    (h : ℝ) (character : ℂ)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (functional_nonzero : functional ≠ 0)
    (eigenlaw : ∀ value,
      functional (positiveMellinQuarterEnergyTranslation h value) =
        character * functional value) :
    ‖character‖ = 1 := by
  let isometry := positiveMellinQuarterEnergyTranslationIsometry h
  have norm_comp :
      ‖functional.comp isometry.toContinuousLinearEquiv.toContinuousLinearMap‖ =
        ‖functional‖ := by
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv functional isometry
  have map_eq :
      functional.comp isometry.toContinuousLinearEquiv.toContinuousLinearMap =
        character • functional := by
    apply ContinuousLinearMap.ext
    intro value
    change functional (positiveMellinQuarterEnergyTranslation h value) =
      character * functional value
    exact eigenlaw value
  have norm_eq : ‖functional‖ = ‖character‖ * ‖functional‖ := by
    calc
      ‖functional‖ =
          ‖functional.comp isometry.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
        norm_comp.symm
      _ = ‖character • functional‖ := congrArg norm map_eq
      _ = ‖character‖ * ‖functional‖ := norm_smul character functional
  have functional_norm_ne_zero : ‖functional‖ ≠ 0 :=
    norm_ne_zero_iff.mpr functional_nonzero
  apply mul_right_cancel₀ functional_norm_ne_zero
  simpa [one_mul] using norm_eq.symm

theorem positiveMellinQuarterEnergy_realPart_eq_quarter
    (parameter : ℂ) (scale : ℝ) (scale_gt_one : 1 < scale)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (functional_nonzero : functional ≠ 0)
    (eigenlaw : ∀ value,
      functional
          (positiveMellinQuarterEnergyTranslation (Real.log scale) value) =
        (scale : ℂ) ^ ((1 / 4 : ℂ) - parameter) * functional value) :
    parameter.re = 1 / 4 := by
  have character_norm :=
    positiveMellinQuarterEnergy_character_norm_eq_one
      (Real.log scale)
      ((scale : ℂ) ^ ((1 / 4 : ℂ) - parameter))
      functional functional_nonzero eigenlaw
  have scale_positive : 0 < scale := lt_trans zero_lt_one scale_gt_one
  have scale_cast : (scale : ℂ) = (scale : ℝ) := by norm_num
  rw [scale_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos scale_positive] at character_norm
  have exponent_zero : ((1 / 4 : ℂ) - parameter).re = 0 := by
    apply (Real.strictMono_rpow_of_base_gt_one scale_gt_one).injective
    simpa using character_norm
  simp at exponent_zero
  linarith

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
