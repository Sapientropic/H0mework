import H0mework.Versions.Y.Arithmetic.PrimeLeakage.AllPrimeRawEffect

/-!
# Faithful all-prime joint relation face

The free integral prime current is sent injectively to the actual
source-boundary relation family at the source-generated stages `p²-3`.  Every
linear combination is killed by the installed joint evaluator because it is
a combination of actual source relations, while its raw integral sibling
remains injective.

The resulting generated face is attached to the exact root occurrence of the
single depth-zero cofinal history.  It is not an independent prime table, a
comparison object or a finite determinant premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect
namespace AllPrimeCofinal

open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimeScaleRuntime
open PrimeScaleCofinal

noncomputable section

/-- Integral-linear combination of the full source-boundary relations. -/
def allPrimeJointRelationMap :
    AllPrimeCurrent →ₗ[ℤ] (RuntimeJointRelationGenerator →₀ ℤ) :=
  (Finsupp.liftAddHom fun prime =>
    AddMonoidHom.flip
      (smulAddHom ℤ (RuntimeJointRelationGenerator →₀ ℤ))
      (runtimeJointSourceBoundaryStageRelation
        (primeRuntimeStage prime))).toIntLinearMap

@[simp] theorem allPrimeJointRelationMap_single
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeJointRelationMap (Finsupp.single prime coefficient) =
      coefficient • runtimeJointSourceBoundaryStageRelation
        (primeRuntimeStage prime) := by
  simp [allPrimeJointRelationMap]

/-- Every source-generated all-prime combination is an actual joint relation.
-/
theorem allPrimeJointRelationMap_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : AllPrimeCurrent) :
    runtimeJointRelationEvaluator observation nontrivial
        (allPrimeJointRelationMap current) = 0 := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      rw [map_add, map_add, leftHypothesis, rightHypothesis, add_zero]
  | single prime coefficient =>
      rw [allPrimeJointRelationMap_single, map_smul,
        runtimeJointSourceBoundaryStageRelation_evaluates_zero, smul_zero]

/-- The source-seed coordinate reads back the exact prime coefficient. -/
theorem allPrimeJointRelationMap_sourceSeed_coordinate
    (current : AllPrimeCurrent) (prime : Nat.Primes) :
    allPrimeJointRelationMap current
        (primeRuntimeStage prime, .sourceSeed) = current prime := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      rw [map_add, Finsupp.add_apply, leftHypothesis, rightHypothesis]
      rfl
  | single other coefficient =>
      rw [allPrimeJointRelationMap_single]
      by_cases other_eq : other = prime
      · subst other
        simp [runtimeJointSourceBoundaryStageRelation,
          runtimeJointRelationAtom]
      · have stage_ne : primeRuntimeStage other ≠ primeRuntimeStage prime :=
          fun stage_eq => other_eq (primeRuntimeStage_injective stage_eq)
        simp [runtimeJointSourceBoundaryStageRelation,
          runtimeJointRelationAtom, stage_ne, other_eq]

theorem allPrimeJointRelationMap_injective :
    Function.Injective allPrimeJointRelationMap := by
  intro left right equality
  ext prime
  rw [← allPrimeJointRelationMap_sourceSeed_coordinate left prime,
    ← allPrimeJointRelationMap_sourceSeed_coordinate right prime,
    equality]

/-- Generated joint face with both faithful integral and faithful relation
coordinates.  Its constructor is private so consumers cannot substitute
caller-provided maps. -/
structure GeneratedAllPrimeCofinalJointFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : Type where
  private mk ::
  relationMap :
    AllPrimeCurrent →ₗ[ℤ] (RuntimeJointRelationGenerator →₀ ℤ)
  boundaryStateMap :
    AllPrimeCurrent →ₗ[ℤ] PairedOmegaJointRelationCarrier
  integralMap : AllPrimeCurrent →ₗ[ℤ] IntegralScaleCarrier
  selectedMap : AllPrimeCurrent →ₗ[ℤ] ℂ
  reversalMap : AllPrimeCurrent →ₗ[ℤ] ℂ
  relationMap_injective : Function.Injective relationMap
  integralMap_injective : Function.Injective integralMap
  relationsSound : ∀ current,
    runtimeJointRelationEvaluator observation nontrivial
      (relationMap current) = 0
  integralSquare :
    runtimeJointIntegralFace.comp boundaryStateMap = integralMap
  selectedSquare :
    (ClozelGeneralizedDual.CenteredGram.selectedGraphCharacterEvaluation
      observation nontrivial).comp integralMap = selectedMap
  reversalSquare :
    (ClozelGeneralizedDual.CenteredGram.reversalGraphCharacterEvaluation
      observation nontrivial).comp integralMap = reversalMap

def generatedAllPrimeCofinalJointFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GeneratedAllPrimeCofinalJointFaceAt observation nontrivial where
  relationMap := allPrimeJointRelationMap
  boundaryStateMap := allPrimeRuntimeBoundaryStateMap observation nontrivial
  integralMap := allPrimeRawEffectMap
  selectedMap := allPrimeSelectedCharacterMap observation nontrivial
  reversalMap := allPrimeReversalCharacterMap observation nontrivial
  relationMap_injective := allPrimeJointRelationMap_injective
  integralMap_injective := allPrimeRawEffectMap_injective
  relationsSound := allPrimeJointRelationMap_evaluates_zero
    observation nontrivial
  integralSquare := allPrimeRuntimeBoundary_integral_square
    observation nontrivial
  selectedSquare := rfl
  reversalSquare := rfl

/-- The generated face is a dependent payload of the exact occurrence which
generated the one depth-zero cofinal history. -/
def allPrimeJointRelationOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (runtimeJointFaithfulStepAt observation nontrivial 0).history.root.map
    fun occurrence =>
      (occurrence, generatedAllPrimeCofinalJointFace observation nontrivial)

theorem allPrimeJointRelationOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (allPrimeJointRelationOccurrence observation nontrivial).map Prod.fst =
      (runtimeJointFaithfulStepAt observation nontrivial 0).history.root := by
  rw [allPrimeJointRelationOccurrence, RootedAccountedUnfolding.map_map]
  change
    (runtimeJointFaithfulStepAt observation nontrivial 0).history.root.map id = _
  exact RootedAccountedUnfolding.map_id _

end
end AllPrimeCofinal
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
