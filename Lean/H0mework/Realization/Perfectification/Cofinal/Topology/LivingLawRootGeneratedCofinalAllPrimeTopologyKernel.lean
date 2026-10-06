import H0mework.Realization.Completion.HistorySettlement
import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionNaturalityKernel
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.UniformSpace.Separation

/-!
The topology observation below is computed from the original cofinal presented
carrier's integral action. No prime, observation datum, or separation branch is
chosen at the source mouth. The kernel records everything this observation
forgets, including infinitely divisible coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory
open CofinalHistorySettlement
open SourceGeneratedPrimePowerCompletion

noncomputable section

universe u

variable {L : Type u} [AddCommGroup L]

/-- All prime-power observations of one integral carrier, with no selected prime. -/
abbrev AllPrimeCompletion (L : Type u) [AddCommGroup L] :=
  (prime : Nat.Primes) → Completion (L := L) prime

def allPrimeMap : L →ₗ[ℤ] AllPrimeCompletion L :=
  LinearMap.pi fun prime => canonicalLinearMap (L := L) prime

theorem allPrime_restriction (prime : Nat.Primes) (stage : Nat) (value : L) :
    (restriction (L := L) prime stage).hom ((allPrimeMap (L := L) value) prime) =
      stageProjection (L := L) prime stage value := by
  have equation := ConcreteCategory.congr_hom
    (canonicalMap_restriction (L := L) prime stage) value
  exact equation

abbrev AllPrimeKernel : Submodule ℤ L := LinearMap.ker (allPrimeMap (L := L))

theorem allPrimeKernel_iff (value : L) :
    value ∈ AllPrimeKernel (L := L) ↔
      ∀ prime : Nat.Primes, ∀ stage : Nat,
        ∃ divided : L, (prime.1 : ℤ) ^ (stage + 1) • divided = value := by
  rw [AllPrimeKernel, LinearMap.mem_ker]
  constructor
  · intro invisible prime stage
    have atPrime : canonicalLinearMap (L := L) prime value = 0 := by
      exact congrFun invisible prime
    exact (canonicalMap_eq_zero_iff prime value).1 atPrime stage
  · intro divided
    funext prime
    exact (canonicalMap_eq_zero_iff prime value).2 (divided prime)

abbrev AllPrimeFaithfulCoimage := L ⧸ AllPrimeKernel (L := L)

def allPrimeCoimageMap :
    AllPrimeFaithfulCoimage (L := L) →ₗ[ℤ] AllPrimeCompletion L :=
  (AllPrimeKernel (L := L)).liftQ (allPrimeMap (L := L)) le_rfl

theorem allPrimeCoimageMap_injective :
    Function.Injective (allPrimeCoimageMap (L := L)) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem allPrimeCoimage_square :
    (allPrimeCoimageMap (L := L)).comp
        (Submodule.mkQ (AllPrimeKernel (L := L))) =
      allPrimeMap (L := L) := by
  exact Submodule.liftQ_mkQ _ _ _

/-- Every stage quotient observation, indexed by both prime and stage. -/
abbrev AllStageObservation (L : Type u) [AddCommGroup L] :=
  (prime : Nat.Primes) → (stage : Nat) → StageResidual (L := L) prime stage

def allStageMap : L →ₗ[ℤ] AllStageObservation L :=
  LinearMap.pi fun prime =>
    LinearMap.pi fun stage => stageProjection (L := L) prime stage

/-- Product of the discrete stage-quotient uniformities. This retains the
    whole prime/stage inventory and requires no selected observation. -/
abbrev allStageUniformity : UniformSpace (AllStageObservation L) := by
  letI : ∀ prime : Nat.Primes, ∀ stage : Nat,
      UniformSpace (StageResidual (L := L) prime stage) :=
    fun _ _ => ⊥
  letI : ∀ prime : Nat.Primes,
      UniformSpace ((stage : Nat) → StageResidual (L := L) prime stage) :=
    fun prime => Pi.uniformSpace (fun stage => StageResidual (L := L) prime stage)
  exact Pi.uniformSpace fun prime =>
    (stage : Nat) → StageResidual (L := L) prime stage

/-- The original integral carrier receives the actual observation topology. -/
abbrev allStageSourceUniformity : UniformSpace L :=
  UniformSpace.comap (allStageMap (L := L)) (allStageUniformity (L := L))

theorem allStage_zero_iff_kernel (value : L) :
    allStageMap (L := L) value = 0 ↔ value ∈ AllPrimeKernel (L := L) := by
  rw [allPrimeKernel_iff]
  constructor
  · intro invisible prime stage
    have atStage := congrFun (congrFun invisible prime) stage
    change stageProjection (L := L) prime stage value = 0 at atStage
    exact (stageProjection_eq_zero_iff prime stage value).1 atStage
  · intro divided
    funext prime stage
    change stageProjection (L := L) prime stage value = 0
    exact (stageProjection_eq_zero_iff prime stage value).2
      (divided prime stage)

theorem allStage_target_t2 :
    @T2Space (AllStageObservation L)
      (allStageUniformity (L := L)).toTopologicalSpace := by
  letI : ∀ prime : Nat.Primes, ∀ stage : Nat,
      UniformSpace (StageResidual (L := L) prime stage) :=
    fun _ _ => ⊥
  letI : ∀ prime : Nat.Primes,
      UniformSpace ((stage : Nat) → StageResidual (L := L) prime stage) :=
    fun prime => Pi.uniformSpace (fun stage => StageResidual (L := L) prime stage)
  letI : UniformSpace (AllStageObservation L) :=
    allStageUniformity (L := L)
  infer_instance

theorem source_inseparable_zero_iff_kernel (value : L) :
    @Inseparable L (allStageSourceUniformity (L := L)).toTopologicalSpace
      value 0 ↔ value ∈ AllPrimeKernel (L := L) := by
  letI : UniformSpace L := allStageSourceUniformity (L := L)
  letI : UniformSpace (AllStageObservation L) :=
    allStageUniformity (L := L)
  have target_t0 : @T0Space (AllStageObservation L)
      (allStageUniformity (L := L)).toTopologicalSpace := by
    haveI := allStage_target_t2 (L := L)
    infer_instance
  rw [inseparable_iff_ker_uniformity, uniformity_comap, Filter.ker_comap]
  rw [t0Space_iff_ker_uniformity.mp target_t0]
  simp only [Set.mem_preimage, Set.mem_diagonal_iff]
  change allStageMap (L := L) value = allStageMap (L := L) 0 ↔
    value ∈ AllPrimeKernel (L := L)
  rw [map_zero]
  exact allStage_zero_iff_kernel value

variable {Root : Type u} {Generator : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}

/-- A generated token indexed by the actual relation history. The observation
    is derived from its quotient action and cannot be installed by a caller. -/
structure TopologicalAt
    (face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence) where
  private mk ::

namespace TopologicalAt

def generate
    (face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence) : TopologicalAt face :=
  ⟨⟩

def observation
    {face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence}
    (_generated : TopologicalAt face) :
    face.CompletionCarrier →ₗ[ℤ]
      AllPrimeCompletion face.CompletionCarrier :=
  allPrimeMap (L := face.CompletionCarrier)

abbrev uniformity
    {face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence}
    (_generated : TopologicalAt face) :
    UniformSpace face.CompletionCarrier :=
  allStageSourceUniformity (L := face.CompletionCarrier)

theorem inseparable_zero_iff_kernel
    {face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence}
    (generated : TopologicalAt face)
    (value : face.CompletionCarrier) :
    @Inseparable face.CompletionCarrier
        generated.uniformity.toTopologicalSpace value 0 ↔
      value ∈ LinearMap.ker generated.observation := by
  exact source_inseparable_zero_iff_kernel value

end TopologicalAt

def topologicalAt
    (face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence) : TopologicalAt face :=
  TopologicalAt.generate face

theorem topologicalAt_restriction
    (face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence)
    (prime : Nat.Primes) (stage : Nat) (value : face.CompletionCarrier) :
    (restriction (L := face.CompletionCarrier) prime stage).hom
      ((topologicalAt face).observation value prime) =
        stageProjection (L := face.CompletionCarrier) prime stage value := by
  exact allPrime_restriction prime stage value

theorem topologicalAt_full_kernel
    (face : RootGeneratedCofinalHistoryAt
      rootOccurrence seedOccurrence continuationOccurrence)
    (value : face.CompletionCarrier) :
    value ∈ LinearMap.ker (topologicalAt face).observation ↔
      ∀ prime : Nat.Primes, ∀ stage : Nat,
        ∃ divided : face.CompletionCarrier,
          (prime.1 : ℤ) ^ (stage + 1) • divided = value := by
  exact allPrimeKernel_iff value

end
end CofinalAllPrimeTopology
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
