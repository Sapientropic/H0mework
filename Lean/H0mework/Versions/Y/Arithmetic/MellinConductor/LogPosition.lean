import H0mework.Realization.Operators.LogPositionTranslation
import H0mework.Versions.Y.Arithmetic.MellinConductor.OwnerWeightedTheta

/-!
# Direct-theta log-position cone for the Müntz dilation family

Positive dilations become translations in the quarter-density logarithmic
chart.  The exact position--translation commutator therefore generates the
logarithmic Euler convolution current on every finite prefix.  This file is
deliberately upstream of any Hilbert boundedness or closability claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace LogPositionCone

open CanonicalArithmeticState.AllPlaceEulerLog
open CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open GenericFoundation.Analysis.LogPositionTranslationCone
open GenericFoundation.Arithmetic.DirichletLogPosition
open scoped ArithmeticFunction SchwartzMap

noncomputable section

def quarterLogTranslationWeight (index : Nat) : ℝ :=
  Real.exp (-Real.log (index + 1 : Nat) / 4)

def normalizedLogDilationTerm
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (state : RawLogState) : RawLogState :=
  fun x =>
    (coefficients (index + 1) : ℂ) *
      (quarterLogTranslationWeight index : ℂ) *
        rawLogTranslate (Real.log (index + 1 : Nat)) state x

def normalizedLogDilationPrefix
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  fun x => ∑ index ∈ Finset.range cutoff,
    normalizedLogDilationTerm coefficients index state x

theorem normalizedLogDilationPrefix_add
    (left right : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) :
    normalizedLogDilationPrefix (left + right) cutoff state =
      normalizedLogDilationPrefix left cutoff state +
        normalizedLogDilationPrefix right cutoff state := by
  funext x
  unfold normalizedLogDilationPrefix normalizedLogDilationTerm
  simp only [ArithmeticFunction.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index membership
  push_cast
  ring

theorem normalizedLogDilationTerm_commutator
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (state : RawLogState) :
    normalizedLogDilationTerm coefficients index (rawLogPosition state) -
        rawLogPosition (normalizedLogDilationTerm coefficients index state) =
      normalizedLogDilationTerm (logPosition coefficients) index state := by
  funext x
  simp [normalizedLogDilationTerm, rawLogPosition,
    rawLogTranslate, logPosition_apply]
  ring

theorem normalizedLogDilationPrefix_commutator
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) :
    normalizedLogDilationPrefix coefficients cutoff (rawLogPosition state) -
        rawLogPosition (normalizedLogDilationPrefix coefficients cutoff state) =
      normalizedLogDilationPrefix
        (logPosition coefficients) cutoff state := by
  funext x
  unfold normalizedLogDilationPrefix rawLogPosition
  simp only [Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index membership
  have term := congrFun
    (normalizedLogDilationTerm_commutator coefficients index state) x
  change normalizedLogDilationTerm coefficients index
        (rawLogPosition state) x -
      (x : ℂ) * normalizedLogDilationTerm coefficients index state x =
    normalizedLogDilationTerm (logPosition coefficients) index state x
  simpa only [Pi.sub_apply, rawLogPosition] using term

def ownerNormalizedLogDilationPrefix
    (owner : GlobalGermOwner) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  normalizedLogDilationPrefix
    (ownerRealCoefficients owner) cutoff state

def ownerEulerConvolutionLogDilationPrefix
    (owner : GlobalGermOwner) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  normalizedLogDilationPrefix
    ((GeneratedEulerLogFaceAt.generate owner).coefficients *
      ownerRealCoefficients owner) cutoff state

def ownerEulerConvolutionResidualCoefficients
    (owner : GlobalGermOwner) : ArithmeticFunction ℝ :=
  (GeneratedEulerLogFaceAt.generate owner).coefficients *
    (ownerRealCoefficients owner - 1)

theorem ownerEulerConvolutionCoefficients_decomposition
    (owner : GlobalGermOwner) :
    (GeneratedEulerLogFaceAt.generate owner).coefficients *
        ownerRealCoefficients owner =
      (GeneratedEulerLogFaceAt.generate owner).coefficients +
        ownerEulerConvolutionResidualCoefficients owner := by
  unfold ownerEulerConvolutionResidualCoefficients
  ring

theorem ownerEulerConvolutionResidualCoefficients_primePower
    (owner : GlobalGermOwner)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    ownerEulerConvolutionResidualCoefficients owner
        ((prime : Nat) ^ exponent) =
      ((exponent : ℝ) - 1) * Real.log ((prime : Nat) : ℝ) := by
  have decompositionAt := congrArg
    (fun coefficients : ArithmeticFunction ℝ =>
      coefficients ((prime : Nat) ^ exponent))
    (ownerEulerConvolutionCoefficients_decomposition owner)
  rw [GeneratedEulerLogFaceAt.generate_convolution_eq_log] at decompositionAt
  simp only [ArithmeticFunction.log_apply,
    ArithmeticFunction.add_apply] at decompositionAt
  rw [GeneratedEulerLogFaceAt.generate_coefficients,
    ArithmeticFunction.vonMangoldt_apply_pow positive.ne',
    ArithmeticFunction.vonMangoldt_apply_prime prime.property] at decompositionAt
  have castPower :
      (((prime : Nat) ^ exponent : Nat) : ℝ) =
        (((prime : Nat) : ℝ) ^ exponent) := by
    norm_cast
  rw [castPower, Real.log_pow] at decompositionAt
  linarith

def ownerEulerRetainedLogDilationPrefix
    (owner : GlobalGermOwner) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  normalizedLogDilationPrefix
    (GeneratedEulerLogFaceAt.generate owner).coefficients cutoff state

def ownerEulerResidualLogDilationPrefix
    (owner : GlobalGermOwner) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  normalizedLogDilationPrefix
    (ownerEulerConvolutionResidualCoefficients owner) cutoff state

theorem ownerEulerConvolutionLogDilationPrefix_decomposition
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    ownerEulerConvolutionLogDilationPrefix owner cutoff state =
      ownerEulerRetainedLogDilationPrefix owner cutoff state +
        ownerEulerResidualLogDilationPrefix owner cutoff state := by
  unfold ownerEulerConvolutionLogDilationPrefix
    ownerEulerRetainedLogDilationPrefix
    ownerEulerResidualLogDilationPrefix
  rw [ownerEulerConvolutionCoefficients_decomposition,
    normalizedLogDilationPrefix_add]

theorem ownerNormalizedLogDilationPrefix_commutator
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    ownerNormalizedLogDilationPrefix owner cutoff (rawLogPosition state) -
        rawLogPosition (ownerNormalizedLogDilationPrefix owner cutoff state) =
      ownerEulerConvolutionLogDilationPrefix owner cutoff state := by
  unfold ownerNormalizedLogDilationPrefix
    ownerEulerConvolutionLogDilationPrefix
  rw [normalizedLogDilationPrefix_commutator]
  have coefficientIdentity :
      logPosition (ownerRealCoefficients owner) =
        (GeneratedEulerLogFaceAt.generate owner).coefficients *
          ownerRealCoefficients owner := by
    rw [logPosition_ownerRealCoefficients_eq_log,
      GeneratedEulerLogFaceAt.generate_convolution_eq_log]
  rw [coefficientIdentity]

def evenSourceLogQuarterState
    (test : SchwartzMap ℝ ℂ) : RawLogState :=
  fun x => (Real.exp (x / 4) : ℂ) *
    coPoissonMuntzEvenSource test (Real.exp x)

theorem normalizedLogDilationTerm_evenSource
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    normalizedLogDilationTerm coefficients index
        (evenSourceLogQuarterState test) x =
      (Real.exp (x / 4) : ℂ) *
        arithmeticPositiveDilationTerm coefficients test
          (Real.exp x) index := by
  have indexPositive : (0 : ℝ) < (index + 1 : Nat) := by
    exact_mod_cast Nat.succ_pos index
  have expShift :
      Real.exp (x + Real.log (index + 1 : Nat)) =
        ((index + 1 : Nat) : ℝ) * Real.exp x := by
    rw [Real.exp_add, Real.exp_log indexPositive]
    ring
  have quarterReal :
      Real.exp (-Real.log (index + 1 : Nat) / 4) *
          Real.exp ((x + Real.log (index + 1 : Nat)) / 4) =
        Real.exp (x / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have quarterComplex :
      (Real.exp (-Real.log (index + 1 : Nat) / 4) : ℂ) *
          (Real.exp ((x + Real.log (index + 1 : Nat)) / 4) : ℂ) =
        (Real.exp (x / 4) : ℂ) := by
    exact_mod_cast quarterReal
  unfold normalizedLogDilationTerm evenSourceLogQuarterState
    rawLogTranslate quarterLogTranslationWeight
    arithmeticPositiveDilationTerm
  change (coefficients (index + 1) : ℂ) *
      (Real.exp (-Real.log (index + 1 : Nat) / 4) : ℂ) *
        ((Real.exp ((x + Real.log (index + 1 : Nat)) / 4) : ℂ) *
          coPoissonMuntzEvenSource test
            (Real.exp (x + Real.log (index + 1 : Nat)))) = _
  rw [expShift]
  rw [← mul_assoc,
    show (coefficients (index + 1) : ℂ) *
          (Real.exp (-Real.log (index + 1 : Nat) / 4) : ℂ) *
          (Real.exp ((x + Real.log (index + 1 : Nat)) / 4) : ℂ) =
        (coefficients (index + 1) : ℂ) *
          (Real.exp (x / 4) : ℂ) by
      rw [mul_assoc, quarterComplex]]
  ring

theorem normalizedLogDilationPrefix_evenSource
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    normalizedLogDilationPrefix coefficients cutoff
        (evenSourceLogQuarterState test) x =
      (Real.exp (x / 4) : ℂ) *
        arithmeticPositiveDilationPrefix coefficients test
          (Real.exp x) cutoff := by
  unfold normalizedLogDilationPrefix
    arithmeticPositiveDilationPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index membership
  exact normalizedLogDilationTerm_evenSource
    coefficients index test x

/-- The direct theta-scale raw cone: one owner action, one source state, and
the Euler convolution current forced by their commutator.  The existing
Quarter-Mellin graph uses a separate square-root chart. -/
theorem ownerDirectThetaLogPositionCone
    (owner : GlobalGermOwner) (test : SchwartzMap ℝ ℂ)
    (cutoff : Nat) :
    ownerNormalizedLogDilationPrefix owner cutoff
          (rawLogPosition (evenSourceLogQuarterState test)) -
        rawLogPosition (ownerNormalizedLogDilationPrefix owner cutoff
          (evenSourceLogQuarterState test)) =
      ownerEulerConvolutionLogDilationPrefix owner cutoff
        (evenSourceLogQuarterState test) :=
  ownerNormalizedLogDilationPrefix_commutator owner cutoff _

theorem ownerDirectThetaLogPositionCone_decomposition
    (owner : GlobalGermOwner) (test : SchwartzMap ℝ ℂ)
    (cutoff : Nat) :
    ownerNormalizedLogDilationPrefix owner cutoff
          (rawLogPosition (evenSourceLogQuarterState test)) -
        rawLogPosition (ownerNormalizedLogDilationPrefix owner cutoff
          (evenSourceLogQuarterState test)) =
      ownerEulerRetainedLogDilationPrefix owner cutoff
          (evenSourceLogQuarterState test) +
        ownerEulerResidualLogDilationPrefix owner cutoff
          (evenSourceLogQuarterState test) := by
  rw [ownerDirectThetaLogPositionCone,
    ownerEulerConvolutionLogDilationPrefix_decomposition]

end
end LogPositionCone
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
