import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateGraphSourceMorphism

/-!
# Conjugate--Tate parameter and value involution

The high-chart parameter is involutive. Pointwise conjugation commutes with the
actual half-weight Tate involution, so applying the source map twice returns
the original positive-Mellin function.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex

noncomputable section

@[simp]
theorem conjugateTateMellinParameter_involutive (z : ℂ) :
    conjugateTateMellinParameter
        (conjugateTateMellinParameter z) = z := by
  simp [conjugateTateMellinParameter]

private theorem star_positiveHalfWeight (t : PositiveMellinReal) :
    star ((t.1 : ℂ) ^ (-(1 / 2 : ℂ))) =
      (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have weightCast :
      (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) =
        ((t.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_cpow t.2.le (-(1 / 2 : ℝ)) using 1
    all_goals norm_num
  rw [weightCast, Complex.star_def, Complex.conj_ofReal]

theorem positiveMellinPointwiseConjugation_tate_commutes
    (value : ClozelPositiveMellinFunction) :
    positiveMellinPointwiseConjugation
        (positiveTateInvolution value) =
      positiveTateInvolution
        (positiveMellinPointwiseConjugation value) := by
  funext t
  change star (((t.1 : ℂ) ^ (-(1 / 2 : ℂ))) *
      value ⟨t.1⁻¹, inv_pos.mpr t.2⟩) =
    (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      star (value ⟨t.1⁻¹, inv_pos.mpr t.2⟩)
  rw [star_mul, star_positiveHalfWeight]
  ring

theorem conjugateTateQuarterMellinTest_involutive_value
    (z : ℂ) (value : QuarterMellinL2Test z) :
    ((conjugateTateQuarterMellinTest
      (conjugateTateMellinParameter z))
        (conjugateTateQuarterMellinTest z value)).1 = value.1 := by
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (positiveTateInvolution
          (positiveMellinPointwiseConjugation value.1))) = value.1
  rw [positiveMellinPointwiseConjugation_tate_commutes,
    positiveMellinPointwiseConjugation_involutive,
    positiveTateInvolution_involutive]

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
