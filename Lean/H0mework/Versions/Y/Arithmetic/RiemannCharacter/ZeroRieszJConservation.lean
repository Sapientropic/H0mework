import H0mework.Versions.Y.Arithmetic.RiemannCharacter.ZeroRieszFullCharacter
import H0mework.Arithmetic.CoPoisson.RelationQuotient

/-!
# Riesz-generated J conservation

The two source.2 Riesz characters define an integral-linear current on the
theta/Fourier role carrier.  It kills every literal prime-power Poisson
relation and therefore descends to the existing presented carrier.  At every
positive scale the raw selected amplitude times the conjugate reversal
amplitude is one.

This is genuine paired conservation.  A concrete reciprocal-pair
counterexample prevents it from being mislabeled as single-mode no-flux.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character
namespace GlobalCoPoissonCurrent

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open ClozelGeneralizedDual.ThetaJRoleRelationQuotient

noncomputable section

/-- Complex conjugation viewed only as an integral-linear map. -/
def complexConjugationZ : ℂ →ₗ[ℤ] ℂ :=
  Complex.conjAe.toLinearEquiv.toLinearMap.restrictScalars ℤ

@[simp] theorem complexConjugationZ_apply (value : ℂ) :
    complexConjugationZ value = star value :=
  rfl

/-- The source.2-generated J-current on the two theta roles. -/
def rieszJFunctional
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    JRoleCarrier →ₗ[ℤ] ℂ :=
  (selectedRieszFullEvaluation observation nontrivial).coprod
    (complexConjugationZ.comp
      (reversalRieszFullEvaluation observation nontrivial))

@[simp] theorem rieszJFunctional_inl
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : IntegralScaleCarrier) :
    rieszJFunctional observation nontrivial
        (LinearMap.inl ℤ IntegralScaleCarrier IntegralScaleCarrier value) =
      selectedRieszFullEvaluation observation nontrivial value := by
  simp [rieszJFunctional]

@[simp] theorem rieszJFunctional_inr
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : IntegralScaleCarrier) :
    rieszJFunctional observation nontrivial
        (LinearMap.inr ℤ IntegralScaleCarrier IntegralScaleCarrier value) =
      star (reversalRieszFullEvaluation observation nontrivial value) := by
  simp [rieszJFunctional, complexConjugationZ]

theorem complexPowerCharacter_inverse_positive
    (coordinate : ℂ) (value : ℝ) (positive : 0 < value) :
    complexPowerCharacter coordinate
        (positiveRealUnit value positive)⁻¹ =
      (value : ℂ) ^ coordinate := by
  rw [map_inv, complexPowerCharacter_apply]
  rw [← Complex.cpow_neg]
  congr 2
  ring

/-- Selected inverse-scale response equals the scale-weighted conjugate
reversal response, independently of a zero or critical-line equation. -/
theorem positiveCharacter_J_identity
    (coordinate : ℂ) (value : ℝ) (positive : 0 < value) :
    (value : ℂ) ^ coordinate =
      (value : ℂ) * star ((value : ℂ) ^
        (-(coordinateReversal coordinate))) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  calc
    Complex.exp (Complex.log (value : ℂ) * coordinate) =
        Complex.exp (Complex.log (value : ℂ) +
          star (Complex.log (value : ℂ) *
            (-(coordinateReversal coordinate)))) := by
      congr 1
      rw [← Complex.ofReal_log positive.le]
      simp [coordinateReversal]
      ring
    _ = Complex.exp (Complex.log (value : ℂ)) *
        Complex.exp (star (Complex.log (value : ℂ) *
          (-(coordinateReversal coordinate)))) := by
      rw [Complex.exp_add]
    _ = Complex.exp (Complex.log (value : ℂ)) *
        star (Complex.exp (Complex.log (value : ℂ) *
          (-(coordinateReversal coordinate)))) := by
      congr 1
      change Complex.exp ((starRingEnd ℂ) _) =
        (starRingEnd ℂ) (Complex.exp _)
      exact Complex.exp_conj _
    _ = (value : ℂ) *
        star (Complex.exp (Complex.log (value : ℂ) *
          (-(coordinateReversal coordinate)))) := by
      rw [Complex.exp_log (Complex.ofReal_ne_zero.mpr positive.ne')]

theorem complexPowerCharacter_primePower_J
    (coordinate : ℂ) (prime : Nat.Primes) (exponent : Nat) :
    complexPowerCharacter coordinate
        ((primePowerUnit prime exponent)⁻¹) =
      thetaDistributionPrimePower prime exponent •
        star (complexPowerCharacter (coordinateReversal coordinate)
          (primePowerUnit prime exponent)) := by
  unfold primePowerUnit
  rw [complexPowerCharacter_inverse_positive]
  rw [complexPowerCharacter_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_eq_mul]
  exact positiveCharacter_J_identity coordinate
    (thetaDistributionPrimePower prime exponent : ℝ)
    (by exact_mod_cast thetaDistributionPrimePower_pos prime exponent)

/-- The Riesz-generated current kills every literal prime-power Poisson
relation. -/
theorem rieszJFunctional_primePowerRelation_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    rieszJFunctional observation nontrivial
        (primePowerRelation prime exponent) = 0 := by
  rw [primePowerRelation, map_sub, map_nsmul,
    rieszJFunctional_inl, rieszJFunctional_inr,
    selectedRieszFullEvaluation_eq_sourceCharacter,
    reversalRieszFullEvaluation_eq_sourceCharacter,
    characterEvaluation_delta, characterEvaluation_delta]
  apply sub_eq_zero.mpr
  change complexPowerCharacter observation.coordinate
      ((primePowerUnit prime exponent)⁻¹) =
    thetaDistributionPrimePower prime exponent •
      star (complexPowerCharacter
        (coordinateReversal observation.coordinate)
        (primePowerUnit prime exponent))
  exact complexPowerCharacter_primePower_J
    observation.coordinate prime exponent

theorem poissonRelations_le_ker_rieszJFunctional
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PoissonRelationSubmodule ≤
      LinearMap.ker (rieszJFunctional observation nontrivial) := by
  rw [PoissonRelationSubmodule, Submodule.span_le]
  rintro _ ⟨index, rfl⟩
  change rieszJFunctional observation nontrivial
      (primePowerRelationFamily index) = 0
  exact rieszJFunctional_primePowerRelation_eq_zero
    observation nontrivial index.1 index.2

/-- J-current descended through the same presented carrier as the actual
theta representation. -/
def presentedRieszJFunctional
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PresentedCarrier →ₗ[ℤ] ℂ :=
  PoissonRelationSubmodule.liftQ
    (rieszJFunctional observation nontrivial)
    (poissonRelations_le_ker_rieszJFunctional observation nontrivial)

@[simp] theorem presentedRieszJFunctional_projection
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (presentedRieszJFunctional observation nontrivial).comp
        presentedProjection =
      rieszJFunctional observation nontrivial := by
  unfold presentedRieszJFunctional presentedProjection
  exact Submodule.liftQ_mkQ _ _ _

/-- Readout retained on the part of the presented carrier not yet explained
by the actual theta representation. -/
def remainingCouplingRieszReadout
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RemainingCouplingResidual →ₗ[ℤ] ℂ :=
  (presentedRieszJFunctional observation nontrivial).domRestrict
    RemainingCouplingResidual

theorem star_positive_cpow
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

/-- Raw half-density Riesz amplitudes preserve their paired J-current at
every positive scale. -/
theorem occurrence_rawRieszAmplitude_paired_stationarity
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    selectedDilationTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive *
      star (reversalDilationTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive) = 1 := by
  rw [occurrence_selectedDilationTrace_eq_character
      observation nontrivial scale positive,
    occurrence_reversalDilationTrace_eq_character
      observation nontrivial scale positive,
    star_positive_cpow _ scale positive]
  rw [← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  have exponentZero :
      ((1 / 4 : ℂ) - selectedCoPoissonMuntzParameter observation) +
        star ((1 / 4 : ℂ) -
          reversalCoPoissonMuntzParameter observation) = 0 := by
    simp [selectedCoPoissonMuntzParameter,
      reversalCoPoissonMuntzParameter, coordinateReversal]
    ring
  rw [exponentZero, Complex.cpow_zero]

/-- Exact deletion witness: reciprocal-product conservation alone cannot be
rebranded as equality of two positive norms. -/
theorem pairedProductConservation_does_not_force_normEquality :
    ∃ selected reversal : ℝ,
      0 < selected ∧ 0 < reversal ∧
        selected * reversal = 1 ∧ selected ≠ reversal := by
  exact ⟨2, 1 / 2, by norm_num⟩

end

end GlobalCoPoissonCurrent
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
