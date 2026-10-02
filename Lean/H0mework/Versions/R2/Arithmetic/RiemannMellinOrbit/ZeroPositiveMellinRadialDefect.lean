import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinTateOrbit
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ZeroPositiveParameter
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ParitySeparator

/-!
# Zero-owned radial character defect

The selected and reversal completed zeros generate two positive Mellin orbit
quotients.  On each quotient the same canonical normalized low-correction
class has functional value one, so its forward q-rich dilation reads the
actual Mellin character.  The difference of the two character norms is the
precise radial obstruction: its vanishing forces the existing C separator to
vanish, without assuming a Hilbert form, self-adjointness, or same-class data.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open InverseZeroFibre

noncomputable section

def selectedPositiveMellinRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule (observation.coordinate / 2) :=
  positiveClozelMellinRelation owner (observation.coordinate / 2)
    (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1

theorem selectedPositiveMellinRelation_annihilated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinFunctional (observation.coordinate / 2)
        (selectedPositiveMellinRelation observation nontrivial) = 0 := by
  change positiveMellinFunctional (observation.coordinate / 2)
      (restrictPositiveMellin _
        ⟨generatedClozelGaussianRemainderKernel owner,
          (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
            observation nontrivial).1⟩) = 0
  rw [positiveMellinFunctional_restrictPositive]
  exact (generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
    observation nontrivial).2

def selectedPositiveMellinDilationReadback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  positiveDomainMellinOrbitQuotientFunctional
    (observation.coordinate / 2)
    (selectedPositiveMellinRelation observation nontrivial)
    (selectedPositiveMellinRelation_annihilated observation nontrivial)
    (positiveDomainMellinOrbitQuotientDilation
      (observation.coordinate / 2)
      (selectedPositiveMellinRelation observation nontrivial)
      (blockQRichSuccessorScale stage : ℝ) (by
        rw [blockQRichSuccessorScale_eq_stage_add_three]
        positivity)
      (positiveNormalizedLowCorrectionClass
        (observation.coordinate / 2)
        (selectedPositiveParameter_re_pos observation nontrivial)
        (selectedPositiveMellinRelation observation nontrivial)))

def reversalPositiveMellinDilationReadback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  positiveDomainMellinOrbitQuotientFunctional
    (coordinateReversal observation.coordinate / 2)
    (reversalPositiveMellinRelation observation nontrivial)
    (reversalPositiveMellinRelation_annihilated observation nontrivial)
    (positiveDomainMellinOrbitQuotientDilation
      (coordinateReversal observation.coordinate / 2)
      (reversalPositiveMellinRelation observation nontrivial)
      (blockQRichSuccessorScale stage : ℝ) (by
        rw [blockQRichSuccessorScale_eq_stage_add_three]
        positivity)
      (positiveNormalizedLowCorrectionClass
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveParameter_re_pos observation nontrivial)
        (reversalPositiveMellinRelation observation nontrivial)))

theorem selectedPositiveMellinDilationReadback_eq_character
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    selectedPositiveMellinDilationReadback observation nontrivial stage =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(observation.coordinate / 2)) := by
  exact positiveDomainMellinOrbitQuotientFunctional_dilation_normalizedLow
    (observation.coordinate / 2)
    (selectedPositiveParameter_re_pos observation nontrivial)
    (selectedPositiveMellinRelation observation nontrivial)
    (selectedPositiveMellinRelation_annihilated observation nontrivial)
    (blockQRichSuccessorScale stage : ℝ) (by
      rw [blockQRichSuccessorScale_eq_stage_add_three]
      positivity)

theorem reversalPositiveMellinDilationReadback_eq_character
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    reversalPositiveMellinDilationReadback observation nontrivial stage =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
  exact positiveDomainMellinOrbitQuotientFunctional_dilation_normalizedLow
    (coordinateReversal observation.coordinate / 2)
    (reversalPositiveParameter_re_pos observation nontrivial)
    (reversalPositiveMellinRelation observation nontrivial)
    (reversalPositiveMellinRelation_annihilated observation nontrivial)
    (blockQRichSuccessorScale stage : ℝ) (by
      rw [blockQRichSuccessorScale_eq_stage_add_three]
      positivity)

def zeroOwnedPositiveMellinRadialDefect
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℝ :=
  ‖selectedPositiveMellinDilationReadback observation nontrivial stage‖ -
    ‖reversalPositiveMellinDilationReadback observation nontrivial stage‖

theorem qRichSuccessorScale_real_one_lt (stage : Nat) :
    1 < (blockQRichSuccessorScale stage : ℝ) := by
  rw [blockQRichSuccessorScale_eq_stage_add_three]
  exact_mod_cast (show 1 < stage + 3 by omega)

theorem coordinate_re_eq_half_of_zeroOwnedPositiveMellinRadialDefect_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (radialZero :
      zeroOwnedPositiveMellinRadialDefect
        observation nontrivial stage = 0) :
    observation.coordinate.re = 1 / 2 := by
  have normEq :
      ‖(blockQRichSuccessorScale stage : ℂ) ^
          (-(observation.coordinate / 2))‖ =
        ‖(blockQRichSuccessorScale stage : ℂ) ^
          (-(coordinateReversal observation.coordinate / 2))‖ := by
    rw [← selectedPositiveMellinDilationReadback_eq_character
        observation nontrivial stage,
      ← reversalPositiveMellinDilationReadback_eq_character
        observation nontrivial stage]
    exact sub_eq_zero.mp radialZero
  have scalePositive : 0 < (blockQRichSuccessorScale stage : ℝ) :=
    lt_trans zero_lt_one (qRichSuccessorScale_real_one_lt stage)
  have scaleCast :
      (blockQRichSuccessorScale stage : ℂ) =
        ((blockQRichSuccessorScale stage : ℝ) : ℂ) := by
    norm_num
  rw [scaleCast,
    Complex.norm_cpow_eq_rpow_re_of_pos scalePositive,
    Complex.norm_cpow_eq_rpow_re_of_pos scalePositive] at normEq
  have exponentEq :=
    (Real.strictMono_rpow_of_base_gt_one
      (qRichSuccessorScale_real_one_lt stage)).injective normEq
  have parameterReEq :
      (observation.coordinate / 2).re =
        (coordinateReversal observation.coordinate / 2).re := by
    apply neg_injective
    simpa using exponentEq
  rw [div_ofNat_re, div_ofNat_re] at parameterReEq
  simp [coordinateReversal] at parameterReEq
  linarith

theorem zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (critical : observation.coordinate.re = 1 / 2) :
    zeroOwnedPositiveMellinRadialDefect
        observation nontrivial stage = 0 := by
  rw [zeroOwnedPositiveMellinRadialDefect,
    selectedPositiveMellinDilationReadback_eq_character,
    reversalPositiveMellinDilationReadback_eq_character,
    sub_eq_zero]
  have scalePositive : 0 < (blockQRichSuccessorScale stage : ℝ) :=
    lt_trans zero_lt_one (qRichSuccessorScale_real_one_lt stage)
  have scaleCast :
      (blockQRichSuccessorScale stage : ℂ) =
        ((blockQRichSuccessorScale stage : ℝ) : ℂ) := by
    norm_num
  rw [scaleCast,
    Complex.norm_cpow_eq_rpow_re_of_pos scalePositive,
    Complex.norm_cpow_eq_rpow_re_of_pos scalePositive]
  congr 1
  simp [coordinateReversal, div_ofNat_re]
  linarith

theorem zeroOwnedPositiveMellinRadialDefect_eq_zero_iff
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    zeroOwnedPositiveMellinRadialDefect observation nontrivial stage = 0 ↔
      observation.coordinate.re = 1 / 2 :=
  ⟨coordinate_re_eq_half_of_zeroOwnedPositiveMellinRadialDefect_zero
      observation nontrivial stage,
    zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
      observation nontrivial stage⟩

theorem coordinate_eq_reversal_of_zeroOwnedPositiveMellinRadialDefect_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (radialZero :
      zeroOwnedPositiveMellinRadialDefect
        observation nontrivial stage = 0) :
    observation.coordinate = coordinateReversal observation.coordinate := by
  have realPart :=
    coordinate_re_eq_half_of_zeroOwnedPositiveMellinRadialDefect_zero
      observation nontrivial stage radialZero
  apply Complex.ext
  · simp [coordinateReversal]
    linarith
  · simp [coordinateReversal]

theorem clozelJCrossCoefficient_eq_zero_of_radialDefect_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (radialZero :
      zeroOwnedPositiveMellinRadialDefect
        observation nontrivial stage = 0) :
    clozelJCrossCoefficient observation.coordinate = 0 := by
  rw [clozelJCrossCoefficient_eq_coordinateResidual]
  exact sub_eq_zero.mpr
    (coordinate_eq_reversal_of_zeroOwnedPositiveMellinRadialDefect_zero
      observation nontrivial stage radialZero)

theorem zeroOwnedPositiveMellinRadialDefect_eq_zero_iff_clozelJCross
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    zeroOwnedPositiveMellinRadialDefect observation nontrivial stage = 0 ↔
      clozelJCrossCoefficient observation.coordinate = 0 := by
  rw [zeroOwnedPositiveMellinRadialDefect_eq_zero_iff,
    clozelJCrossCoefficient_eq_coordinateResidual]
  constructor
  · intro critical
    apply sub_eq_zero.mpr
    apply Complex.ext
    · simp [coordinateReversal]
      linarith
    · simp [coordinateReversal]
  · intro crossZero
    have fixed := sub_eq_zero.mp crossZero
    have realFixed := congrArg Complex.re fixed
    simp [coordinateReversal] at realFixed
    linarith

theorem branchNormalizedQRichSeparator_eq_zero_of_radialDefect_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (radialZero :
      zeroOwnedPositiveMellinRadialDefect
        observation nontrivial characterStage = 0) :
    branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation) stage row = 0 := by
  rw [mathlibLeft_branchNormalizedSeparator_eq_clozelCross,
    clozelJCrossCoefficient_eq_zero_of_radialDefect_zero
      observation nontrivial characterStage radialZero,
    mul_zero]

end

end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
