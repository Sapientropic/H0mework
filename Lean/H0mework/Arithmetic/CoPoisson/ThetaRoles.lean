import H0mework.Realization.Integral.CharacterGroupRing
import H0mework.Realization.Topology.PositiveRealCharacter
import H0mework.Arithmetic.CoPoisson.FirstResidual

/-!
# Theta J-role representation of the integral character group ring

The two copies of `ℤ[(ℝ≥0)ˣ]` generate the theta and Fourier-theta roles.
Poisson summation kills the literal prime-power J-relation.  No zero,
separator, fixedness, or Riemann-hypothesis premise enters the construction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace ThetaJRoleRepresentation

open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

abbrev IntegralScaleCarrier :=
  SourceGeneratedIntegralCharacterGroupRing.Carrier (Units NNReal)

/-- Binary J-role carrier, the module biproduct of the theta and
Fourier-theta group rings. -/
abbrev JRoleCarrier := IntegralScaleCarrier × IntegralScaleCarrier

def scaleValue (scale : Units NNReal) : ℝ :=
  ((scale : NNReal) : ℝ)

theorem scaleValue_pos (scale : Units NNReal) :
    0 < scaleValue scale :=
  by
    exact_mod_cast
      (show (0 : NNReal) < (scale : NNReal) from
        pos_iff_ne_zero.mpr scale.ne_zero)

@[simp] theorem scaleValue_mul (left right : Units NNReal) :
    scaleValue (left * right) = scaleValue left * scaleValue right := by
  simp [scaleValue]

def thetaAtScale (scale : Units NNReal) : ComplexTempered :=
  coPoissonMuntzThetaDistribution (scaleValue scale)
    (scaleValue_pos scale).ne'

theorem thetaDistribution_congr
    {left right : ℝ} (equality : left = right)
    (leftNe : left ≠ 0) (rightNe : right ≠ 0) :
    coPoissonMuntzThetaDistribution left leftNe =
      coPoissonMuntzThetaDistribution right rightNe := by
  subst right
  rfl

theorem thetaAtScale_mul (left right : Units NNReal) :
    thetaAtScale (left * right) =
      thetaDistributionScalePull (scaleValue left)
        (scaleValue_pos left).ne' (thetaAtScale right) := by
  unfold thetaAtScale
  calc
    _ = coPoissonMuntzThetaDistribution
        (scaleValue left * scaleValue right)
        (mul_ne_zero (scaleValue_pos left).ne'
          (scaleValue_pos right).ne') :=
      thetaDistribution_congr (scaleValue_mul left right) _ _
    _ = _ := (thetaDistributionScalePull_thetaDistribution
      (scaleValue left) (scaleValue right)
      (scaleValue_pos left).ne' (scaleValue_pos right).ne').symm

/-- The left basis role sends `δ_a` to the actual scaled theta
distribution. -/
def leftRole : IntegralScaleCarrier →ₗ[ℤ] ComplexTempered :=
  canonicalBasis.constr ℤ thetaAtScale

/-- The right basis role is the Fourier transform of that same actual theta
distribution. -/
def rightRole : IntegralScaleCarrier →ₗ[ℤ] ComplexTempered :=
  canonicalBasis.constr ℤ
    (fun scale ↦ FourierTransform.fourier (thetaAtScale scale))

@[simp] theorem leftRole_delta (scale : Units NNReal) :
    leftRole (delta scale) = thetaAtScale scale := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

@[simp] theorem rightRole_delta (scale : Units NNReal) :
    rightRole (delta scale) =
      FourierTransform.fourier (thetaAtScale scale) := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

/-- Source left translation is the actual scale pull on the theta role. -/
theorem leftRole_translation_covariance (scale : Units NNReal) :
    leftRole.comp (leftTranslation scale).toLinearMap =
      ((thetaDistributionScalePull (scaleValue scale)
        (scaleValue_pos scale).ne').restrictScalars ℤ).toLinearMap.comp
          leftRole := by
  apply MonoidAlgebra.lhom_ext'
  intro basisScale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single basisScale coefficient =
      coefficient • delta basisScale by simp [delta]]
  simp only [map_smul]
  congr 1
  change leftRole (leftTranslation scale (delta basisScale)) = _
  rw [leftTranslation_delta, leftRole_delta, leftRole_delta,
    thetaAtScale_mul]
  rfl

/-- Actual Z-linear J-role representation. -/
def representation : JRoleCarrier →ₗ[ℤ] ComplexTempered :=
  leftRole.coprod rightRole

@[simp] theorem representation_inl (value : IntegralScaleCarrier) :
    representation (LinearMap.inl ℤ _ _ value) = leftRole value := by
  simp [representation]

@[simp] theorem representation_inr (value : IntegralScaleCarrier) :
    representation (LinearMap.inr ℤ _ _ value) = rightRole value := by
  simp [representation]

def primePowerUnit (prime : Nat.Primes) (exponent : Nat) : Units NNReal :=
  positiveRealUnit (thetaDistributionPrimePower prime exponent : ℝ)
    (by exact_mod_cast thetaDistributionPrimePower_pos prime exponent)

@[simp] theorem primePowerUnit_value
    (prime : Nat.Primes) (exponent : Nat) :
    scaleValue (primePowerUnit prime exponent) =
      (thetaDistributionPrimePower prime exponent : ℝ) := by
  exact positiveRealUnit_val _ _

def inversePrimePowerUnit (prime : Nat.Primes) (exponent : Nat) :
    Units NNReal :=
  (primePowerUnit prime exponent)⁻¹

theorem inversePrimePowerUnit_eq_inv
    (prime : Nat.Primes) (exponent : Nat) :
    inversePrimePowerUnit prime exponent =
      (primePowerUnit prime exponent)⁻¹ := by
  rfl

@[simp] theorem inversePrimePowerUnit_value
    (prime : Nat.Primes) (exponent : Nat) :
    scaleValue (inversePrimePowerUnit prime exponent) =
      1 / (thetaDistributionPrimePower prime exponent : ℝ) := by
  unfold inversePrimePowerUnit scaleValue
  rw [Units.val_inv_eq_inv_val]
  change (scaleValue (primePowerUnit prime exponent))⁻¹ = _
  rw [primePowerUnit_value]
  simp [one_div]

theorem leftRole_primePower_inverse
    (prime : Nat.Primes) (exponent : Nat) :
    leftRole (delta ((primePowerUnit prime exponent)⁻¹)) =
      thetaDistributionWhole prime exponent := by
  rw [← inversePrimePowerUnit_eq_inv, leftRole_delta]
  unfold thetaAtScale thetaDistributionWhole
  exact thetaDistribution_congr
    (inversePrimePowerUnit_value prime exponent) _ _

theorem rightRole_primePower
    (prime : Nat.Primes) (exponent : Nat) :
    rightRole (delta (primePowerUnit prime exponent)) =
      thetaDistributionQuotient prime exponent := by
  rw [rightRole_delta]
  unfold thetaAtScale thetaDistributionQuotient
  exact congrArg FourierTransform.fourier
    (thetaDistribution_congr (primePowerUnit_value prime exponent) _ _)

/-- Literal J-relation `inl δ_(q⁻¹) - q • inr δ_q`. -/
def primePowerRelation (prime : Nat.Primes) (exponent : Nat) :
    JRoleCarrier :=
  LinearMap.inl ℤ IntegralScaleCarrier IntegralScaleCarrier
      (delta ((primePowerUnit prime exponent)⁻¹)) -
    thetaDistributionPrimePower prime exponent •
      LinearMap.inr ℤ IntegralScaleCarrier IntegralScaleCarrier
        (delta (primePowerUnit prime exponent))

/-- Existing distribution-level Poisson summation kills the actual
prime-power J-relation. -/
theorem representation_primePowerRelation_eq_zero
    (prime : Nat.Primes) (exponent : Nat) :
    representation (primePowerRelation prime exponent) = 0 := by
  rw [primePowerRelation, map_sub, map_nsmul,
    representation_inl, representation_inr,
    leftRole_primePower_inverse, rightRole_primePower,
    thetaDistributionWhole_eq_primePower_nsmul_quotient, sub_self]

end
end ThetaJRoleRepresentation
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
