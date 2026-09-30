import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import H0mework.Arithmetic.EulerGlobal.CoordinateGerm

/-!
# The Euler logarithmic face of the global determinant germ

The global determinant occurrence already owns its full arithmetic-function
coefficient carrier.  This file exposes the von Mangoldt function as the
unique logarithmic convolution face of that same carrier.  No analytic value,
zero, logarithmic derivative, or nonvanishing statement enters the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace AllPlaceEulerLog

open ArithmeticGeneration
open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticRuntimeCofinalEuler
open Filter
open RootedAccountedUnfolding
open scoped ArithmeticFunction

noncomputable section

abbrev GlobalGermOwner :=
  CanonicalUnitArithmeticFactorizationEulerDependentDiagram.FactorizationPayload ×
    GeneratedGlobalDeterminantCoordinateGerm

/-- Every generated determinant germ has the same coefficient function.  The
proof reads the germ's own eventual-prefix certificate; it does not replace
the germ by the distinguished root occurrence. -/
theorem generatedGermCoefficients_eq_zeta
    (germ : GeneratedGlobalDeterminantCoordinateGerm) :
    germ.coefficients =
      (ArithmeticFunction.zeta : ArithmeticFunction ℚ) := by
  rw [← castArithmeticFunction_zeta, ← formalEulerCoefficients_eq_zeta]
  apply ArithmeticFunction.ext
  intro coefficient
  have together :=
    (germ.generated coefficient).and
      (runtimeDeterminantCoordinatePrefix_eventually_eq coefficient)
  rcases together.exists with ⟨stage, generatedEq, formalEq⟩
  exact generatedEq.symm.trans formalEq

/-- The real coefficient carrier is obtained by scalar extension from the
literal owner coefficients. -/
def ownerRealCoefficients (owner : GlobalGermOwner) :
    ArithmeticFunction ℝ :=
  ⟨fun n => (owner.2.coefficients n : ℝ), by simp⟩

@[simp] theorem ownerRealCoefficients_apply
    (owner : GlobalGermOwner) (n : ℕ) :
    ownerRealCoefficients owner n =
      (owner.2.coefficients n : ℝ) :=
  rfl

theorem ownerRealCoefficients_eq_zeta
    (owner : GlobalGermOwner) :
    ownerRealCoefficients owner =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  apply ArithmeticFunction.ext
  intro n
  have coefficientEq :
      owner.2.coefficients n =
        (ArithmeticFunction.zeta : ArithmeticFunction ℚ) n :=
    congrArg (fun value : ArithmeticFunction ℚ => value n)
      (generatedGermCoefficients_eq_zeta owner.2)
  rw [ownerRealCoefficients_apply, coefficientEq]
  by_cases zero : n = 0
  · subst n
    simp
  · simp [ArithmeticFunction.zeta_apply_ne zero]

/-- The logarithmic Euler face generated over one exact global-germ owner.
The private constructor prevents a caller from submitting an unrelated
arithmetic function satisfying a later analytic equation. -/
structure GeneratedEulerLogFaceAt (owner : GlobalGermOwner) : Type where
  private mk ::
  coefficients : ArithmeticFunction ℝ
  coefficients_eq_vonMangoldt :
    coefficients = ArithmeticFunction.vonMangoldt
  convolution_eq_log :
    coefficients * ownerRealCoefficients owner = ArithmeticFunction.log

namespace GeneratedEulerLogFaceAt

def generate (owner : GlobalGermOwner) :
    GeneratedEulerLogFaceAt owner where
  coefficients := ArithmeticFunction.vonMangoldt
  coefficients_eq_vonMangoldt := rfl
  convolution_eq_log := by
    rw [ownerRealCoefficients_eq_zeta]
    exact ArithmeticFunction.vonMangoldt_mul_zeta

@[simp] theorem generate_coefficients (owner : GlobalGermOwner) :
    (generate owner).coefficients = ArithmeticFunction.vonMangoldt :=
  rfl

theorem generate_convolution_eq_log (owner : GlobalGermOwner) :
    (generate owner).coefficients * ownerRealCoefficients owner =
      ArithmeticFunction.log :=
  (generate owner).convolution_eq_log

/-- The owner relation determines the Euler-log coefficients uniquely.
This is the arithmetic inverse-fibre calculation: multiplication by the
same owner zeta carrier is cancelled by its generated Möbius inverse. -/
theorem eq_vonMangoldt_of_convolution_eq_log
    (owner : GlobalGermOwner)
    (candidate : ArithmeticFunction ℝ)
    (relation :
      candidate * ownerRealCoefficients owner = ArithmeticFunction.log) :
    candidate = ArithmeticFunction.vonMangoldt := by
  rw [ownerRealCoefficients_eq_zeta] at relation
  calc
    candidate = candidate * 1 := (mul_one candidate).symm
    _ = candidate *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by
      rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = (candidate *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      rw [mul_assoc]
    _ = ArithmeticFunction.log *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      rw [relation]
    _ = ArithmeticFunction.vonMangoldt :=
      ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

theorem unique_of_convolution_eq_log
    (owner : GlobalGermOwner)
    (candidate : ArithmeticFunction ℝ)
    (relation :
      candidate * ownerRealCoefficients owner = ArithmeticFunction.log) :
    candidate = (generate owner).coefficients := by
  rw [generate_coefficients]
  exact eq_vonMangoldt_of_convolution_eq_log owner candidate relation

end GeneratedEulerLogFaceAt

abbrev EulerLogPayload :=
  Σ owner : GlobalGermOwner, GeneratedEulerLogFaceAt owner

/-- The Euler-log carrier is a dependent face of the literal global-germ
occurrence, not a sibling arithmetic source. -/
def globalEulerLogOccurrence :
    RootedAccountedUnfolding EulerLogPayload :=
  globalGermOccurrence.map fun owner =>
    ⟨owner, GeneratedEulerLogFaceAt.generate owner⟩

theorem globalEulerLogOccurrence_projects :
    globalEulerLogOccurrence.map Sigma.fst = globalGermOccurrence := by
  unfold globalEulerLogOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change globalGermOccurrence.map id = globalGermOccurrence
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem globalEulerLogOccurrence_root_owner :
    globalEulerLogOccurrence.root.1 = globalGermOccurrence.root :=
  rfl

theorem globalEulerLogOccurrence_root_convolution :
    globalEulerLogOccurrence.root.2.coefficients *
        ownerRealCoefficients globalEulerLogOccurrence.root.1 =
      ArithmeticFunction.log :=
  globalEulerLogOccurrence.root.2.convolution_eq_log

end
end AllPlaceEulerLog
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
