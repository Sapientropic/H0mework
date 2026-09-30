import H0mework.Versions.Y.Arithmetic.RiemannGraph.PrimePowerMuntzSourceCurrent
import H0mework.Versions.Y.Arithmetic.MellinConductor.LogPosition

/-!
# Runtime Müntz conductor cofinal current

The installed Euler conductor acts on the actual positive-dilation Schwartz
family.  Finite prefixes have an exact successor write whose forced trace is
the next source term.  At a prime power that trace carries the primitive
Euler weight `log p`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor

open ClozelGeneralizedDual
open ClozelGeneralizedDual.MuntzConductor
open ClozelGeneralizedDual.MuntzConductor.LogPositionCone
open Material
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open PrimePower.Quadratic
open Quadratic
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.Consumer

noncomputable section

def runtimeFaceConductorDilationTerm
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (index : Nat) : ℂ :=
  arithmeticPositiveDilationTerm
    face.eulerConductorCurrent test scale index

def runtimeFaceConductorDilationPrefix
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) : ℂ :=
  arithmeticPositiveDilationPrefix
    face.eulerConductorCurrent test scale cutoff

theorem runtimeFaceConductorDilationPrefix_succ
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    runtimeFaceConductorDilationPrefix face test scale (cutoff + 1) =
      runtimeFaceConductorDilationPrefix face test scale cutoff +
        runtimeFaceConductorDilationTerm face test scale cutoff :=
  arithmeticPositiveDilationPrefix_succ _ _ _ _

theorem runtimeFaceConductorDilationPrefix_eq_global
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    runtimeFaceConductorDilationPrefix face test scale cutoff =
      generatedEulerConductorDilationPrefix
        globalEulerConductorOccurrence.root.1.1 test scale cutoff := by
  unfold runtimeFaceConductorDilationPrefix
    generatedEulerConductorDilationPrefix
  rw [face.eulerConductorCurrent_eq_global,
    globalEulerConductorOccurrence.root.2.conductorCurrent_eq]

theorem primePowerRuntimeFace_conductorDilationTerm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : SchwartzMap ℝ ℂ) (scale : ℝ)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    runtimeFaceConductorDilationTerm
        (primePowerRuntimeFace observation nontrivial prime exponent)
        test scale ((prime : Nat) ^ exponent - 1) =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        coPoissonMuntzEvenSource test
          ((((prime : Nat) ^ exponent : Nat) : ℝ) * scale) := by
  unfold runtimeFaceConductorDilationTerm
    arithmeticPositiveDilationTerm
  have powerPositive : 0 < (prime : Nat) ^ exponent :=
    pow_pos prime.property.pos _
  rw [Nat.sub_add_cancel powerPositive]
  have currentRead :
      (primePowerRuntimeFace observation nontrivial prime exponent
        ).eulerConductorCurrent ((prime : Nat) ^ exponent) =
        Real.log ((prime : Nat) : ℝ) := by
    simpa [thetaDistributionPrimePower] using
      primePowerRuntimeFace_conductorRead
        observation nontrivial prime exponent positive
  rw [currentRead]

/-- The root owner already generates the existing infinite theta read; the
cofinal conductor prefixes are its exact logarithmic-current sibling. -/
theorem globalOwnerWeightedPositiveDilationSum_eq_thetaNonzero
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (scale_ne : scale ≠ 0) :
    ownerWeightedPositiveDilationSum
        globalEulerConductorOccurrence.root.1.1 test scale =
      coPoissonMuntzThetaNonzero test scale :=
  ownerWeightedPositiveDilationSum_eq_thetaNonzero _ _ scale_ne

theorem runtimeFaceDirectThetaConductorLogPrefix_eq_cofinal
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (cutoff : Nat) (x : ℝ) :
    normalizedLogDilationPrefix face.eulerConductorCurrent cutoff
        (evenSourceLogQuarterState test) x =
      (Real.exp (x / 4) : ℂ) *
        runtimeFaceConductorDilationPrefix face test
          (Real.exp x) cutoff := by
  exact normalizedLogDilationPrefix_evenSource
    face.eulerConductorCurrent cutoff test x

theorem globalOwnerEulerRetainedLogPrefix_eq_runtime
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) (state : GenericFoundation.Analysis.LogPositionTranslationCone.RawLogState) :
    ownerEulerRetainedLogDilationPrefix
        globalEulerConductorOccurrence.root.1.1 cutoff state =
      normalizedLogDilationPrefix
        face.eulerConductorCurrent cutoff state := by
  unfold ownerEulerRetainedLogDilationPrefix
  rw [face.eulerConductorCurrent_eq_global,
    globalEulerConductorOccurrence.root.2.conductorCurrent_eq,
    generatedEulerConductorCurrent_eq_eulerFace]

/-- The raw global cone now lands in the installed runtime retained current
plus a forward source-convolution residual. -/
theorem globalOwnerDirectThetaLogCone_runtime_decomposition
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (test : SchwartzMap ℝ ℂ) (cutoff : Nat) :
    ownerNormalizedLogDilationPrefix
          globalEulerConductorOccurrence.root.1.1 cutoff
          (GenericFoundation.Analysis.LogPositionTranslationCone.rawLogPosition
            (evenSourceLogQuarterState test)) -
        GenericFoundation.Analysis.LogPositionTranslationCone.rawLogPosition
          (ownerNormalizedLogDilationPrefix
            globalEulerConductorOccurrence.root.1.1 cutoff
            (evenSourceLogQuarterState test)) =
      normalizedLogDilationPrefix face.eulerConductorCurrent cutoff
          (evenSourceLogQuarterState test) +
        ownerEulerResidualLogDilationPrefix
          globalEulerConductorOccurrence.root.1.1 cutoff
          (evenSourceLogQuarterState test) := by
  rw [ownerDirectThetaLogPositionCone_decomposition,
    globalOwnerEulerRetainedLogPrefix_eq_runtime face]

end
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
