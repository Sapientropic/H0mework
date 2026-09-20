import H0mework.Arithmetic.CoPoisson.ThetaRoles

/-!
# Actual Müntz coupling for the theta J-role representation

Evaluation on a Schwartz test identifies the two integral group-ring roles
with the existing theta and Fourier-theta formulas.  The Müntz scale
remainder and the prime-power Poisson relation therefore live on the same
actual distribution carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace ThetaJRoleMuntzCoupling

open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation
open scoped SchwartzMap

noncomputable section

/-- A left group-ring basis vector evaluates as the existing actual theta
formula at the same positive scale. -/
@[simp] theorem leftRole_delta_apply
    (scale : Units NNReal) (test : SchwartzMap ℝ ℂ) :
    leftRole (delta scale) test =
      coPoissonMuntzTheta test (scaleValue scale) := by
  rw [ThetaJRoleRepresentation.leftRole_delta]
  exact coPoissonMuntzThetaDistribution_apply _ _ test

/-- A right group-ring basis vector evaluates as the Fourier-test theta
formula at the same positive scale. -/
@[simp] theorem rightRole_delta_apply
    (scale : Units NNReal) (test : SchwartzMap ℝ ℂ) :
    rightRole (delta scale) test =
      coPoissonMuntzTheta (FourierTransform.fourier test)
        (scaleValue scale) := by
  rw [ThetaJRoleRepresentation.rightRole_delta,
    TemperedDistribution.fourier_apply]
  exact coPoissonMuntzThetaDistribution_apply _ _ _

/-- The existing Müntz remainder is the left integral role with its literal
zero mode and volume mode removed. -/
theorem coPoissonMuntzScaleRemainder_eq_leftRole
    (scale : Units NNReal) (test : SchwartzMap ℝ ℂ) :
    coPoissonMuntzScaleRemainder test (scaleValue scale) =
      leftRole (delta scale) test - test 0 -
        (scaleValue scale)⁻¹ • ∫ x : ℝ, test x := by
  rw [coPoissonMuntzScaleRemainder_eq test (scaleValue_pos scale),
    leftRole_delta_apply]
  simp only [coPoissonMuntzTheta]
  abel

/-- The literal prime-power J-relation vanishes after evaluation on every
Schwartz test, with no zero or spectral premise. -/
theorem primePowerRelation_apply_eq_zero
    (prime : Nat.Primes) (exponent : Nat) (test : SchwartzMap ℝ ℂ) :
    representation (primePowerRelation prime exponent) test = 0 := by
  have kernel := congrArg (fun distribution : ComplexTempered =>
    distribution test)
    (representation_primePowerRelation_eq_zero prime exponent)
  simpa using kernel

end
end ThetaJRoleMuntzCoupling
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
