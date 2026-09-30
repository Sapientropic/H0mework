import H0mework.Arithmetic.MellinConductor.DirichletLogPosition
import H0mework.Versions.Y.Arithmetic.EulerLog.GlobalGerm

/-!
# Source-generated Euler conductor current

The global-germ owner supplies its actual Dirichlet coefficient carrier and
its canonical generated Dirichlet inverse.  Commuting logarithmic position through that
owner convolution generates the Euler face itself.  No analytic division by
zeta, zero-free region, or logarithmic derivative is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace AllPlaceEulerLog
namespace Conductor

open GenericFoundation.Arithmetic.DirichletLogPosition
open RootedAccountedUnfolding
open scoped ArithmeticFunction

noncomputable section

theorem logPosition_ownerRealCoefficients_eq_log
    (owner : GlobalGermOwner) :
    logPosition (ownerRealCoefficients owner) =
      ArithmeticFunction.log := by
  rw [ownerRealCoefficients_eq_zeta]
  apply ArithmeticFunction.ext
  intro n
  by_cases zero : n = 0
  · subst n
    simp
  · simp [logPosition_apply,
      ArithmeticFunction.zeta_apply_ne zero]

/-- The current produced by moving logarithmic position past the owner's
left-convolution action. -/
def ownerLogPositionCommutator
    (owner : GlobalGermOwner) (test : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  logPosition (ownerRealCoefficients owner * test) -
    ownerRealCoefficients owner * logPosition test

def ownerEulerConvolutionCurrent
    (owner : GlobalGermOwner) (test : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  (GeneratedEulerLogFaceAt.generate owner).coefficients *
    (ownerRealCoefficients owner * test)

/-- The occurrence-generated coordinate equation: the log-position
commutator is the Euler action on the same convolved state. -/
theorem ownerLogPositionCommutator_eq_eulerConvolution
    (owner : GlobalGermOwner) (test : ArithmeticFunction ℝ) :
    ownerLogPositionCommutator owner test =
      ownerEulerConvolutionCurrent owner test := by
  rw [ownerLogPositionCommutator,
    leftConvolution_commutator,
    logPosition_ownerRealCoefficients_eq_log]
  unfold ownerEulerConvolutionCurrent
  rw [← mul_assoc,
    GeneratedEulerLogFaceAt.generate_convolution_eq_log]

/-- The owner's coefficient at the multiplicative unit is generated as the
unit, hence carries its canonical invertibility evidence. -/
theorem ownerRealCoefficients_one (owner : GlobalGermOwner) :
    ownerRealCoefficients owner 1 = 1 := by
  rw [ownerRealCoefficients_eq_zeta]
  simp

@[instance_reducible] noncomputable def ownerCoefficientOneInvertible
    (owner : GlobalGermOwner) :
    Invertible (ownerRealCoefficients owner 1) :=
  (ownerRealCoefficients_one owner).symm ▸ invertibleOne

/-- The Dirichlet inverse is constructed from the owner's own coefficient
carrier and its generated unit evidence. -/
def generatedOwnerDirichletInverse (owner : GlobalGermOwner) :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.dirichletInverse
    (ownerRealCoefficients owner) (ownerCoefficientOneInvertible owner)

theorem ownerRealCoefficients_mul_generatedOwnerDirichletInverse
    (owner : GlobalGermOwner) :
    ownerRealCoefficients owner * generatedOwnerDirichletInverse owner = 1 :=
  ArithmeticFunction.self_mul_dirichletInverse _ _

/-- Applying the commutator to the source-generated inverse isolates the
Euler conductor current without dividing an analytic value. -/
def generatedEulerConductorCurrent (owner : GlobalGermOwner) :
    ArithmeticFunction ℝ :=
  ownerLogPositionCommutator owner (generatedOwnerDirichletInverse owner)

theorem generatedEulerConductorCurrent_eq_eulerFace
    (owner : GlobalGermOwner) :
    generatedEulerConductorCurrent owner =
      (GeneratedEulerLogFaceAt.generate owner).coefficients := by
  unfold generatedEulerConductorCurrent
  rw [ownerLogPositionCommutator_eq_eulerConvolution]
  unfold ownerEulerConvolutionCurrent
  rw [ownerRealCoefficients_mul_generatedOwnerDirichletInverse, mul_one]

theorem generatedEulerConductorCurrent_primePower
    (owner : GlobalGermOwner)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    generatedEulerConductorCurrent owner ((prime : Nat) ^ exponent) =
      Real.log ((prime : Nat) : ℝ) := by
  rw [generatedEulerConductorCurrent_eq_eulerFace,
    GeneratedEulerLogFaceAt.generate_coefficients,
    ArithmeticFunction.vonMangoldt_apply_pow positive.ne',
    ArithmeticFunction.vonMangoldt_apply_prime prime.property]

/-- The conductor coordinate generated over one exact Euler-log occurrence.
The inverse and current are both fixed by its owner. -/
structure GeneratedEulerConductorFaceAt
    (source : EulerLogPayload) where
  private mk ::
  inverseTest : ArithmeticFunction ℝ
  conductorCurrent : ArithmeticFunction ℝ
  inverseTest_eq : inverseTest = generatedOwnerDirichletInverse source.1
  conductorCurrent_eq : conductorCurrent =
    generatedEulerConductorCurrent source.1
  conductorCurrent_eq_eulerFace : conductorCurrent =
    source.2.coefficients

def generateEulerConductorFace (source : EulerLogPayload) :
    GeneratedEulerConductorFaceAt source where
  inverseTest := generatedOwnerDirichletInverse source.1
  conductorCurrent := generatedEulerConductorCurrent source.1
  inverseTest_eq := rfl
  conductorCurrent_eq := rfl
  conductorCurrent_eq_eulerFace := by
    rw [generatedEulerConductorCurrent_eq_eulerFace,
      GeneratedEulerLogFaceAt.generate_coefficients,
      source.2.coefficients_eq_vonMangoldt]

abbrev EulerConductorPayload :=
  Σ source : EulerLogPayload, GeneratedEulerConductorFaceAt source

/-- The conductor is a dependent child of the canonical global Euler-log
occurrence; no Riemann-zero observation is needed to generate it. -/
def globalEulerConductorOccurrence :
    RootedAccountedUnfolding EulerConductorPayload :=
  globalEulerLogOccurrence.map fun source =>
    ⟨source, generateEulerConductorFace source⟩

theorem globalEulerConductorOccurrence_projects :
    globalEulerConductorOccurrence.map Sigma.fst =
      globalEulerLogOccurrence := by
  rw [globalEulerConductorOccurrence,
    RootedAccountedUnfolding.map_map]
  change globalEulerLogOccurrence.map id = globalEulerLogOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem globalEulerConductorOccurrence_root_current_eq :
    globalEulerConductorOccurrence.root.2.conductorCurrent =
      globalEulerLogOccurrence.root.2.coefficients :=
  globalEulerConductorOccurrence.root.2.conductorCurrent_eq_eulerFace

end
end Conductor
end AllPlaceEulerLog
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
