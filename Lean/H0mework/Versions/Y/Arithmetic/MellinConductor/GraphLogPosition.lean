import H0mework.Versions.Y.Arithmetic.MellinConductor.LogPosition
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzRieszDilation

/-!
# Quarter-Mellin graph chart of the log-position cone

The existing graph carrier uses the square-root co-Poisson chart: its
coordinate `x` reads physical scale `exp (x/2)`.  Hence an integer dilation
uses shift `2 log n`, half-density weight `n⁻¹/²`, and position `x/2`.
These factors are generated here before the source-map quotient is read.
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
namespace GraphLogPositionCone

open CanonicalArithmeticState.AllPlaceEulerLog
open GenericFoundation.Analysis.LogPositionTranslationCone
open GenericFoundation.Arithmetic.DirichletLogPosition
open LogPositionCone
open scoped ArithmeticFunction SchwartzMap

noncomputable section

def graphLogPosition (state : RawLogState) : RawLogState :=
  fun x => ((x / 2 : ℝ) : ℂ) * state x

def graphLogTranslationShift (index : Nat) : ℝ :=
  2 * Real.log (index + 1 : Nat)

def graphHalfDensityWeight (index : Nat) : ℝ :=
  Real.exp (-Real.log (index + 1 : Nat) / 2)

/-- The positive integer `n = index + 1` as an actual integral scale unit. -/
def graphIntegerScaleUnit (index : Nat) : Units NNReal :=
  Units.mk0 (((index + 1 : Nat) : NNReal)) (by
    exact_mod_cast Nat.succ_ne_zero index)

/-- The integer unit acts on the existing Quarter-Mellin graph through the
same squared physical scale used by the installed integral test orbit. -/
def graphIntegerDilationScale (index : Nat) : ℝ :=
  ((((graphIntegerScaleUnit index : Units NNReal) : NNReal) : ℝ)) ^ 2

theorem graphIntegerDilationScale_eq (index : Nat) :
    graphIntegerDilationScale index =
      ((index + 1 : Nat) : ℝ) ^ 2 := by
  rfl

theorem graphIntegerDilationScale_pos (index : Nat) :
    0 < graphIntegerDilationScale index := by
  rw [graphIntegerDilationScale_eq]
  positivity

theorem graphIntegerDilationScale_log (index : Nat) :
    Real.log (graphIntegerDilationScale index) =
      graphLogTranslationShift index := by
  rw [graphIntegerDilationScale_eq]
  unfold graphLogTranslationShift
  rw [Real.log_pow]
  norm_num

def graphNormalizedLogDilationTerm
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (state : RawLogState) : RawLogState :=
  fun x =>
    (coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ) *
        rawLogTranslate (graphLogTranslationShift index) state x

def graphNormalizedLogDilationPrefix
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) : RawLogState :=
  fun x => ∑ index ∈ Finset.range cutoff,
    graphNormalizedLogDilationTerm coefficients index state x

theorem graphNormalizedLogDilationPrefix_add
    (left right : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) :
    graphNormalizedLogDilationPrefix (left + right) cutoff state =
      graphNormalizedLogDilationPrefix left cutoff state +
        graphNormalizedLogDilationPrefix right cutoff state := by
  funext x
  unfold graphNormalizedLogDilationPrefix graphNormalizedLogDilationTerm
  simp only [ArithmeticFunction.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index membership
  push_cast
  ring

theorem graphNormalizedLogDilationTerm_commutator
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (state : RawLogState) :
    graphNormalizedLogDilationTerm coefficients index
          (graphLogPosition state) -
        graphLogPosition
          (graphNormalizedLogDilationTerm coefficients index state) =
      graphNormalizedLogDilationTerm
        (logPosition coefficients) index state := by
  funext x
  simp [graphNormalizedLogDilationTerm, graphLogPosition,
    rawLogTranslate, graphLogTranslationShift, logPosition_apply]
  ring

theorem graphNormalizedLogDilationPrefix_commutator
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (state : RawLogState) :
    graphNormalizedLogDilationPrefix coefficients cutoff
          (graphLogPosition state) -
        graphLogPosition
          (graphNormalizedLogDilationPrefix coefficients cutoff state) =
      graphNormalizedLogDilationPrefix
        (logPosition coefficients) cutoff state := by
  funext x
  unfold graphNormalizedLogDilationPrefix graphLogPosition
  simp only [Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index membership
  have term := congrFun
    (graphNormalizedLogDilationTerm_commutator
      coefficients index state) x
  change graphNormalizedLogDilationTerm coefficients index
        (graphLogPosition state) x -
      ((x / 2 : ℝ) : ℂ) *
        graphNormalizedLogDilationTerm coefficients index state x =
    graphNormalizedLogDilationTerm
      (logPosition coefficients) index state x
  simpa only [Pi.sub_apply, graphLogPosition] using term

def ownerGraphLogDilationPrefix
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    RawLogState :=
  graphNormalizedLogDilationPrefix
    (ownerRealCoefficients owner) cutoff state

def ownerEulerGraphWholePrefix
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    RawLogState :=
  graphNormalizedLogDilationPrefix
    ((GeneratedEulerLogFaceAt.generate owner).coefficients *
      ownerRealCoefficients owner) cutoff state

def ownerEulerGraphRetainedPrefix
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    RawLogState :=
  graphNormalizedLogDilationPrefix
    (GeneratedEulerLogFaceAt.generate owner).coefficients cutoff state

def ownerEulerGraphResidualPrefix
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    RawLogState :=
  graphNormalizedLogDilationPrefix
    (ownerEulerConvolutionResidualCoefficients owner) cutoff state

theorem ownerEulerGraphWholePrefix_decomposition
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    ownerEulerGraphWholePrefix owner cutoff state =
      ownerEulerGraphRetainedPrefix owner cutoff state +
        ownerEulerGraphResidualPrefix owner cutoff state := by
  unfold ownerEulerGraphWholePrefix ownerEulerGraphRetainedPrefix
    ownerEulerGraphResidualPrefix
  rw [ownerEulerConvolutionCoefficients_decomposition,
    graphNormalizedLogDilationPrefix_add]

theorem ownerGraphLogDilationPrefix_commutator
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    ownerGraphLogDilationPrefix owner cutoff (graphLogPosition state) -
        graphLogPosition (ownerGraphLogDilationPrefix owner cutoff state) =
      ownerEulerGraphWholePrefix owner cutoff state := by
  unfold ownerGraphLogDilationPrefix ownerEulerGraphWholePrefix
  rw [graphNormalizedLogDilationPrefix_commutator]
  have coefficientIdentity :
      logPosition (ownerRealCoefficients owner) =
        (GeneratedEulerLogFaceAt.generate owner).coefficients *
          ownerRealCoefficients owner := by
    rw [CanonicalArithmeticState.AllPlaceEulerLog.Conductor.logPosition_ownerRealCoefficients_eq_log,
      GeneratedEulerLogFaceAt.generate_convolution_eq_log]
  rw [coefficientIdentity]

theorem ownerGraphLogPositionCone_decomposition
    (owner : GlobalGermOwner) (cutoff : Nat) (state : RawLogState) :
    ownerGraphLogDilationPrefix owner cutoff (graphLogPosition state) -
        graphLogPosition (ownerGraphLogDilationPrefix owner cutoff state) =
      ownerEulerGraphRetainedPrefix owner cutoff state +
        ownerEulerGraphResidualPrefix owner cutoff state := by
  rw [ownerGraphLogDilationPrefix_commutator,
    ownerEulerGraphWholePrefix_decomposition]

def quarterMellinGraphLogState
    {z : ℂ} (value : QuarterMellinL2Test z) : RawLogState :=
  positiveMellinLogQuarterTransform value.1

/-- The graph logarithmic state reads the actual normalized source dilation
as translation by the logarithm of its physical scale. -/
theorem quarterMellinGraphLogState_dilation
    {z : ℂ} (scale : ℝ) (positive : 0 < scale)
    (value : QuarterMellinL2Test z) (x : ℝ) :
    quarterMellinGraphLogState
        (quarterDilationTestAction z scale positive value) x =
      rawLogTranslate (Real.log scale)
        (quarterMellinGraphLogState value) x := by
  unfold quarterMellinGraphLogState rawLogTranslate
  exact positiveMellinLogQuarterTransform_normalizedDilation
    scale positive value.1 x

/-- Consequently the `n`-th graph term is the actual squared-scale source
orbit, weighted only by its half-density and arithmetic coefficient. -/
theorem graphNormalizedLogDilationTerm_eq_sourceAction
    {z : ℂ} (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (value : QuarterMellinL2Test z) (x : ℝ) :
    graphNormalizedLogDilationTerm coefficients index
        (quarterMellinGraphLogState value) x =
      (coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ) *
          quarterMellinGraphLogState
            (quarterDilationTestAction z
              (graphIntegerDilationScale index)
              (graphIntegerDilationScale_pos index) value) x := by
  unfold graphNormalizedLogDilationTerm
  rw [quarterMellinGraphLogState_dilation,
    graphIntegerDilationScale_log]

def coPoissonQuarterGraphLogState
    (test : SchwartzMap ℝ ℂ) : RawLogState :=
  positiveMellinLogQuarterTransform (coPoissonQuarterMellinMap test)

theorem coPoissonQuarterGraphLogState_eq_halfOrbit
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonQuarterGraphLogState test x =
      coPoissonLogOrbitMap test (x / 2) :=
  positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap test x

theorem graphNormalizedLogDilationTerm_coPoissonChart
    (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    graphNormalizedLogDilationTerm coefficients index
        (coPoissonQuarterGraphLogState test) x =
      (coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ) *
          coPoissonLogOrbitMap test
            (x / 2 + Real.log (index + 1 : Nat)) := by
  unfold graphNormalizedLogDilationTerm rawLogTranslate
    graphLogTranslationShift
  rw [coPoissonQuarterGraphLogState_eq_halfOrbit]
  have argumentEq :
      (x + 2 * Real.log (index + 1 : Nat)) / 2 =
        x / 2 + Real.log (index + 1 : Nat) := by
    ring
  rw [argumentEq]

end
end GraphLogPositionCone
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
