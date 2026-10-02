import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzDilationActionLaws
import H0mework.Arithmetic.SonineSource.StageZeroSonineDilation
import H0mework.Versions.R2.Arithmetic.SonineCoupling.ConjugateTateQuarterMellinTestEquivalence

/-!
# Conjugate--Tate inverse-scale source action

The actual half-density Schwartz dilation is sent by Fourier conjugate--Tate
to inverse dilation.  The same source identity is transported to the lawful
quarter-Mellin carrier, including its generated character normalization.  No
action square, shell equality, radial cancellation, or zero is premise data.
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

open Complex FourierTransform
open ClozelEndpointSourceEffect
open scoped SchwartzMap

noncomputable section

theorem positiveMellinPointwiseConjugation_normalizedDilation
    (scale : ℝ) (positive : 0 < scale)
    (value : ClozelPositiveMellinFunction) :
    positiveMellinPointwiseConjugation
        (positiveMellinQuarterNormalizedDilation scale positive value) =
      positiveMellinQuarterNormalizedDilation scale positive
        (positiveMellinPointwiseConjugation value) := by
  funext t
  change star ((Real.exp (Real.log scale / 4) : ℂ) *
      value ⟨scale * t.1, mul_pos positive t.2⟩) =
    (Real.exp (Real.log scale / 4) : ℂ) *
      star (value ⟨scale * t.1, mul_pos positive t.2⟩)
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring_nf

theorem positiveTateInvolution_normalizedDilation_inverse
    (scale : ℝ) (positive : 0 < scale)
    (value : ClozelPositiveMellinFunction) :
    positiveTateInvolution
        (positiveMellinQuarterNormalizedDilation scale positive value) =
      positiveMellinQuarterNormalizedDilation scale⁻¹
        (inv_pos.mpr positive) (positiveTateInvolution value) := by
  apply positiveMellinLogQuarterTransform_injective
  funext x
  rw [positiveMellinLogQuarterTransform_tate,
    positiveMellinLogQuarterTransform_normalizedDilation,
    positiveMellinLogQuarterTransform_normalizedDilation,
    positiveMellinLogQuarterTransform_tate,
    Real.log_inv]
  ring_nf

theorem conjugateTatePositiveMellin_normalizedDilation_inverse
    (scale : ℝ) (positive : 0 < scale)
    (value : ClozelPositiveMellinFunction) :
    positiveTateInvolution
        (positiveMellinPointwiseConjugation
          (positiveMellinQuarterNormalizedDilation scale positive value)) =
      positiveMellinQuarterNormalizedDilation scale⁻¹
        (inv_pos.mpr positive)
        (positiveTateInvolution
          (positiveMellinPointwiseConjugation value)) := by
  rw [positiveMellinPointwiseConjugation_normalizedDilation,
    positiveTateInvolution_normalizedDilation_inverse]

theorem conjugateTateQuarterMellinTest_rawDilation_inverse
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : QuarterMellinL2Test z) :
    conjugateTateQuarterMellinTest z
        (quarterDilationTestAction z scale positive value) =
      quarterDilationTestAction (conjugateTateMellinParameter z)
        scale⁻¹ (inv_pos.mpr positive)
        (conjugateTateQuarterMellinTest z value) := by
  apply Subtype.ext
  exact conjugateTatePositiveMellin_normalizedDilation_inverse
    scale positive value.1

private theorem star_positive_cpow
    (exponent : ℂ) (value : ℝ) (positive : 0 < value) :
    star ((value : ℂ) ^ exponent) =
      (value : ℂ) ^ star exponent := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  change (starRingEnd ℂ)
      (Complex.exp (Complex.log (value : ℂ) * exponent)) = _
  rw [← Complex.exp_conj]
  congr 1
  rw [← Complex.ofReal_log positive.le]
  simp

private theorem starRingEnd_positive_cpow
    (exponent : ℂ) (value : ℝ) (positive : 0 < value) :
    (starRingEnd ℂ) ((value : ℂ) ^ exponent) =
      (value : ℂ) ^ star exponent := by
  exact star_positive_cpow exponent value positive

theorem schwartzConjugation_coPoissonEnergyTranslation
    (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    schwartzConjugation (coPoissonSchwartzEnergyTranslation shift test) =
      coPoissonSchwartzEnergyTranslation shift
        (schwartzConjugation test) := by
  apply SchwartzMap.ext
  intro x
  change star ((Real.exp shift : ℂ) ^ (1 / 2 : ℂ) *
      test (Real.exp shift * x)) =
    (Real.exp shift : ℂ) ^ (1 / 2 : ℂ) *
      star (test (Real.exp shift * x))
  rw [star_mul,
    star_positive_cpow (1 / 2 : ℂ) (Real.exp shift) (Real.exp_pos shift)]
  simp
  ring_nf

theorem fourier_coPoissonSchwartzEnergyTranslation
    (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    𝓕 (coPoissonSchwartzEnergyTranslation shift test) =
      coPoissonSchwartzEnergyTranslation (-shift) (𝓕 test) := by
  change 𝓕 ((Real.exp shift : ℂ) ^ (1 / 2 : ℂ) •
      scaledSchwartzTest (Real.exp shift) (Real.exp_ne_zero shift) test) = _
  rw [FourierTransform.fourier_smul,
    scaledSchwartzTest_fourier (Real.exp shift) (Real.exp_pos shift)]
  apply SchwartzMap.ext
  intro x
  simp only [smul_apply, scaledSchwartzTest_apply, smul_eq_mul]
  change (Real.exp shift : ℂ) ^ (1 / 2 : ℂ) *
      ((Real.exp shift : ℂ)⁻¹ *
        (𝓕 test) ((Real.exp shift)⁻¹ * x)) =
    (Real.exp (-shift) : ℂ) ^ (1 / 2 : ℂ) *
      (𝓕 test) (Real.exp (-shift) * x)
  rw [Real.exp_neg]
  have halfProduct :
      (Real.exp shift : ℂ) ^ (1 / 2 : ℂ) *
          (Real.exp shift : ℂ)⁻¹ =
        (((Real.exp shift)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    have inversePower :
        (Real.exp shift : ℂ)⁻¹ =
          (Real.exp shift : ℂ) ^ (-(1 : ℂ)) := by
      rw [Complex.cpow_neg, Complex.cpow_one]
    rw [inversePower, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero shift))]
    rw [show (1 / 2 : ℂ) + -(1 : ℂ) = -(1 / 2 : ℂ) by norm_num]
    rw [show (((Real.exp shift)⁻¹ : ℝ) : ℂ) =
      (Real.exp shift : ℂ)⁻¹ by norm_num]
    rw [Complex.inv_cpow_ofReal_nonneg (Real.exp_nonneg shift),
      Complex.cpow_neg]
  rw [← mul_assoc, halfProduct]

/-- Source-level `J D_h = D_{-h} J` with the actual half-density scalar. -/
theorem schwartzTateConjugation_energyTranslation_inverse
    (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    schwartzTateConjugation
        (coPoissonSchwartzEnergyTranslation shift test) =
      coPoissonSchwartzEnergyTranslation (-shift)
        (schwartzTateConjugation test) := by
  change 𝓕 (schwartzConjugation
      (coPoissonSchwartzEnergyTranslation shift test)) = _
  rw [schwartzConjugation_coPoissonEnergyTranslation,
    fourier_coPoissonSchwartzEnergyTranslation]
  rfl

theorem schwartzTateConjugation_stageZeroInverseDilation
    (test : SonineSchwartz) :
    schwartzTateConjugation (stageZeroSonineInverseDilation test) =
      coPoissonSchwartzEnergyTranslation
        (-(Real.log stageZeroSonineQ⁻¹))
        (schwartzTateConjugation test) := by
  exact schwartzTateConjugation_energyTranslation_inverse
    (Real.log stageZeroSonineQ⁻¹) test

private theorem quarterDilationCharacter_star_inv
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    ((starRingEnd ℂ) (quarterDilationCharacter z scale))⁻¹ =
      quarterDilationCharacter (conjugateTateMellinParameter z) scale := by
  unfold quarterDilationCharacter conjugateTateMellinParameter
  rw [starRingEnd_positive_cpow (1 / 4 - z) scale positive,
    ← Complex.cpow_neg]
  congr 2
  simp
  ring_nf

private theorem quarterDilationCharacter_inverse_scale_inv
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    (quarterDilationCharacter z scale⁻¹)⁻¹ =
      quarterDilationCharacter z scale := by
  have product :
      quarterDilationCharacter z scale⁻¹ *
          quarterDilationCharacter z scale = 1 := by
    calc
      _ = quarterDilationCharacter z (scale⁻¹ * scale) :=
        (quarterDilationCharacter_mul z scale⁻¹ scale
          (inv_pos.mpr positive) positive).symm
      _ = quarterDilationCharacter z 1 := by
        rw [inv_mul_cancel₀ positive.ne']
      _ = 1 := quarterDilationCharacter_one z
  apply mul_left_cancel₀
    (quarterDilationCharacter_ne_zero z scale⁻¹
      (inv_pos.mpr positive))
  rw [mul_inv_cancel₀
    (quarterDilationCharacter_ne_zero z scale⁻¹
      (inv_pos.mpr positive)), product]

theorem normalizedQuarterDilationCharacter_conjugate_inverseScale
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    ((starRingEnd ℂ) (quarterDilationCharacter z scale))⁻¹ =
      (quarterDilationCharacter
        (conjugateTateMellinParameter z) scale⁻¹)⁻¹ := by
  rw [quarterDilationCharacter_star_inv z scale positive,
    quarterDilationCharacter_inverse_scale_inv
      (conjugateTateMellinParameter z) scale positive]

/-- Character-normalized source action square on the lawful test carrier. -/
theorem conjugateTateQuarterMellinTest_normalizedDilation_inverse
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : QuarterMellinL2Test z) :
    conjugateTateQuarterMellinTest z
        (normalizedQuarterDilationTestAction z scale positive value) =
      normalizedQuarterDilationTestAction
        (conjugateTateMellinParameter z) scale⁻¹
        (inv_pos.mpr positive)
        (conjugateTateQuarterMellinTest z value) := by
  calc
    _ = ((starRingEnd ℂ) (quarterDilationCharacter z scale))⁻¹ •
        conjugateTateQuarterMellinTest z
          (quarterDilationTestAction z scale positive value) := by
      change conjugateTateQuarterMellinTest z
          ((quarterDilationCharacter z scale)⁻¹ •
            quarterDilationTestAction z scale positive value) = _
      rw [map_smulₛₗ, map_inv₀]
    _ = ((starRingEnd ℂ) (quarterDilationCharacter z scale))⁻¹ •
        quarterDilationTestAction (conjugateTateMellinParameter z)
          scale⁻¹ (inv_pos.mpr positive)
          (conjugateTateQuarterMellinTest z value) := by
      rw [conjugateTateQuarterMellinTest_rawDilation_inverse]
    _ = _ := by
      rw [normalizedQuarterDilationCharacter_conjugate_inverseScale
        z scale positive]
      rfl

end


end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
