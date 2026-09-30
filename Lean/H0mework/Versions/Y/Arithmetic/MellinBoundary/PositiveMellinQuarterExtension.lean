import H0mework.Versions.Y.Arithmetic.MellinBoundary.PositiveMellinQuarterEnergyBoundary
import H0mework.Versions.Y.Arithmetic.MellinBoundary.PositiveMellinQuarterMaterial

/-!
# Exact interface for a quarter-energy Mellin extension

`IsQuarterMellinExtension` is the smallest honest interface for extending
the source Mellin integral to the actual quarter `L²` carrier.  Its low-mode
readback is generated from the existing `Ioc 0 1` correction, so the usual
nonzero-functional premise is derived rather than supplied by a caller.

This file tightens the consumer boundary only.  It does not construct the
extension, a character law, or the radial-defect vanishing producer.
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

def IsQuarterMellinExtension (z : ℂ)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ) : Prop :=
  ∀ f : PositiveMellinQuarterL2,
    MellinConvergent (positiveMellinExtension f.1) z →
      functional (positiveMellinQuarterLpValue f) =
        mellin (positiveMellinExtension f.1) z

theorem isQuarterMellinExtension_low_readback
    {z : ℂ} (hz : 0 < z.re)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (extension : IsQuarterMellinExtension z functional) :
    functional
        (positiveMellinQuarterLpValue
          ⟨positiveClozelLowCorrection,
            positiveClozelLowCorrection_mem_quarterL2⟩) =
      1 / z := by
  rw [extension _ (positiveClozelLowCorrection_positiveMellinConvergent hz)]
  calc
    mellin (positiveMellinExtension positiveClozelLowCorrection) z =
        mellin clozelLowCorrection z := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      simp [positiveMellinExtension, positiveClozelLowCorrection,
        clozelLowCorrection, ht]
    _ = 1 / z := (hasMellin_clozelLowCorrection hz).2

theorem isQuarterMellinExtension_nonzero
    {z : ℂ} (hz : 0 < z.re)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (extension : IsQuarterMellinExtension z functional) :
    functional ≠ 0 := by
  intro functionalZero
  have readback := isQuarterMellinExtension_low_readback hz functional extension
  rw [functionalZero, zero_apply] at readback
  have zNe : z ≠ 0 := by
    intro zZero
    rw [zZero, zero_re] at hz
    exact lt_irrefl 0 hz
  exact (one_div_ne_zero zNe) readback.symm

theorem positiveMellinQuarterEnergy_realPart_eq_quarter_of_extension
    (parameter : ℂ) (scale : ℝ) (scale_gt_one : 1 < scale)
    (parameter_re_pos : 0 < parameter.re)
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (extension : IsQuarterMellinExtension (parameter / 2) functional)
    (eigenlaw : ∀ value,
      functional
          (positiveMellinQuarterEnergyTranslation (Real.log scale) value) =
        (scale : ℂ) ^ ((1 / 4 : ℂ) - parameter / 2) * functional value) :
    parameter.re = 1 / 2 := by
  have positiveParameter : 0 < (parameter / 2).re := by
    rw [div_ofNat_re]
    linarith
  have quarter := positiveMellinQuarterEnergy_realPart_eq_quarter
    (parameter / 2) scale scale_gt_one functional
    (isQuarterMellinExtension_nonzero positiveParameter functional extension)
    eigenlaw
  rw [div_ofNat_re] at quarter
  linarith

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
