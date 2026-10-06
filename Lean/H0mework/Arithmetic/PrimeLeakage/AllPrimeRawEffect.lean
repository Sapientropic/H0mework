import H0mework.Arithmetic.PrimeLeakage.PrimeRawEffect

/-!
# Faithful all-prime raw effect map

The source-generated prime basis extends freely to finite integral currents.
Its raw-effect map is faithful: the coefficient at scale `p` is exactly the
negative source coefficient.  Selected/reversal characters and the full joint
boundary state are sibling maps of this same integral carrier.
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

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimeScaleRuntime
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

abbrev AllPrimeCurrent := Nat.Primes →₀ ℤ

/-- Integral extension of the source-generated prime effects. -/
def allPrimeRawEffectMap : AllPrimeCurrent →ₗ[ℤ] IntegralScaleCarrier :=
  (Finsupp.liftAddHom fun prime =>
    AddMonoidHom.flip (smulAddHom ℤ IntegralScaleCarrier)
      (generatedPrimeRawEffect prime)).toIntLinearMap

@[simp] theorem allPrimeRawEffectMap_single
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeRawEffectMap (Finsupp.single prime coefficient) =
      coefficient • generatedPrimeRawEffect prime := by
  simp [allPrimeRawEffectMap]

/-- The prime-scale coefficient is an exact inverse read of the source
current.  The common identity coefficient cannot hide a prime coordinate. -/
theorem allPrimeRawEffectMap_prime_coordinate
    (current : AllPrimeCurrent) (prime : Nat.Primes) :
    (allPrimeRawEffectMap current).coeff (blockPrimeScaleUnit prime) =
      -current prime := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
        leftHypothesis, rightHypothesis]
      simp [Finsupp.add_apply]
      abel
  | single other coefficient =>
      rw [allPrimeRawEffectMap_single,
        generatedPrimeRawEffect_eq_delta_sub,
        MonoidAlgebra.coeff_smul_apply]
      by_cases other_eq : other = prime
      · subst other
        have one_ne : (1 : Units NNReal) ≠ blockPrimeScaleUnit prime :=
          Ne.symm (blockPrimeScaleUnit_ne_one prime)
        simp [delta, one_ne]
      · have scale_ne :
          blockPrimeScaleUnit other ≠ blockPrimeScaleUnit prime :=
          fun scale_eq => other_eq (blockPrimeScaleUnit_injective scale_eq)
        have one_ne : (1 : Units NNReal) ≠ blockPrimeScaleUnit prime :=
          Ne.symm (blockPrimeScaleUnit_ne_one prime)
        simp [delta, scale_ne, other_eq, one_ne]

theorem allPrimeRawEffectMap_injective :
    Function.Injective allPrimeRawEffectMap := by
  intro left right equality
  ext prime
  have coordinate_eq := congrArg
    (fun value : IntegralScaleCarrier =>
      value.coeff (blockPrimeScaleUnit prime)) equality
  rw [allPrimeRawEffectMap_prime_coordinate,
    allPrimeRawEffectMap_prime_coordinate] at coordinate_eq
  exact neg_injective coordinate_eq

/-- Selected and reversal Riesz characters are sibling reads of the faithful
integral all-prime map. -/
def allPrimeSelectedCharacterMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    AllPrimeCurrent →ₗ[ℤ] ℂ :=
  (selectedGraphCharacterEvaluation observation nontrivial).comp
    allPrimeRawEffectMap

def allPrimeReversalCharacterMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    AllPrimeCurrent →ₗ[ℤ] ℂ :=
  (reversalGraphCharacterEvaluation observation nontrivial).comp
    allPrimeRawEffectMap

@[simp] theorem allPrimeSelectedCharacterMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeSelectedCharacterMap observation nontrivial
        (Finsupp.single prime coefficient) =
      coefficient •
        (1 - installedPrimeEigenvalue prime observation.coordinate) := by
  change selectedGraphCharacterEvaluation observation nontrivial
      (allPrimeRawEffectMap (Finsupp.single prime coefficient)) = _
  rw [allPrimeRawEffectMap_single, map_smul,
    generatedPrimeRawEffect_selected_character]

@[simp] theorem allPrimeReversalCharacterMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeReversalCharacterMap observation nontrivial
        (Finsupp.single prime coefficient) =
      coefficient •
        (1 - installedPrimeEigenvalue prime
          (coordinateReversal observation.coordinate)) := by
  change reversalGraphCharacterEvaluation observation nontrivial
      (allPrimeRawEffectMap (Finsupp.single prime coefficient)) = _
  rw [allPrimeRawEffectMap_single, map_smul,
    generatedPrimeRawEffect_reversal_character]

def allPrimePairedCharacterMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    AllPrimeCurrent →ₗ[ℤ] (ℂ × ℂ) where
  toFun := fun current =>
    (allPrimeSelectedCharacterMap observation nontrivial current,
      allPrimeReversalCharacterMap observation nontrivial current)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

@[simp] theorem allPrimePairedCharacterMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimePairedCharacterMap observation nontrivial
        (Finsupp.single prime coefficient) =
      (coefficient •
          (1 - installedPrimeEigenvalue prime observation.coordinate),
        coefficient •
          (1 - installedPrimeEigenvalue prime
            (coordinateReversal observation.coordinate))) := by
  apply Prod.ext <;> simp [allPrimePairedCharacterMap]

/-- Sibling full-joint state generated by the same prime current. -/
def allPrimeRuntimeBoundaryStateMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    AllPrimeCurrent →ₗ[ℤ] PairedOmegaJointRelationCarrier :=
  (Finsupp.liftAddHom fun prime =>
    AddMonoidHom.flip (smulAddHom ℤ PairedOmegaJointRelationCarrier)
      (runtimeJointRelationGeneratorValue observation nontrivial
        (primeRuntimeStage prime, .sourceBoundary))).toIntLinearMap

@[simp] theorem allPrimeRuntimeBoundaryStateMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeRuntimeBoundaryStateMap observation nontrivial
        (Finsupp.single prime coefficient) =
      coefficient • runtimeJointRelationGeneratorValue observation nontrivial
        (primeRuntimeStage prime, .sourceBoundary) := by
  simp [allPrimeRuntimeBoundaryStateMap]

/-- The integral map is a literal dependent face of the full joint state map.
-/
theorem allPrimeRuntimeBoundary_integral_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    runtimeJointIntegralFace.comp
        (allPrimeRuntimeBoundaryStateMap observation nontrivial) =
      allPrimeRawEffectMap := by
  apply LinearMap.ext
  intro current
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      simp only [map_add, leftHypothesis, rightHypothesis]
  | single prime coefficient =>
      change runtimeJointIntegralFace
          (allPrimeRuntimeBoundaryStateMap observation nontrivial
            (Finsupp.single prime coefficient)) =
        allPrimeRawEffectMap (Finsupp.single prime coefficient)
      rw [allPrimeRuntimeBoundaryStateMap_single,
        allPrimeRawEffectMap_single, map_smul,
        generatedPrimeRawEffect_runtime observation nontrivial prime]

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
