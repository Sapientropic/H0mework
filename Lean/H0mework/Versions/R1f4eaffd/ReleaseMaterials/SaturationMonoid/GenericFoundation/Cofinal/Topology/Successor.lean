import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory SourceGeneratedPrimePowerCompletion

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

/-- The source action supplies every prime-power stage by its existing quotient action. -/
def allStageSuccessor (action : L →ₗ[ℤ] M) : AllStageObservation L →ₗ[ℤ] AllStageObservation M :=
  LinearMap.piMap fun prime => LinearMap.piMap fun stage => stageMap prime stage action

theorem allStage_successor_source (action : L →ₗ[ℤ] M) (value : L) :
    allStageSuccessor action (allStageMap value) = allStageMap (action value) := by
  funext prime stage
  exact LinearMap.congr_fun (stageMap_projection prime stage action) value

def allPrimeSuccessor (action : L →ₗ[ℤ] M) : AllPrimeCompletion L →ₗ[ℤ] AllPrimeCompletion M :=
  LinearMap.piMap fun prime => inducedCompletionLinearMap prime action

theorem allPrime_successor_source (action : L →ₗ[ℤ] M) (value : L) :
    allPrimeSuccessor action (allPrimeMap value) = allPrimeMap (action value) := by
  funext prime
  exact ConcreteCategory.congr_hom (canonicalMap_naturality prime action) value

theorem allPrime_successor_restriction (action : L →ₗ[ℤ] M)
    (prime : Nat.Primes) (stage : Nat) (value : AllPrimeCompletion L) :
    (restriction (L := M) prime stage).hom ((allPrimeSuccessor action value) prime) =
      stageMap prime stage action ((restriction (L := L) prime stage).hom (value prime)) :=
  ConcreteCategory.congr_hom (inducedCompletionMap_restriction prime action stage) (value prime)

/-- The complete stage observation is uniformly transported by the actual action. -/
theorem allStage_successor_uniformContinuous (action : L →ₗ[ℤ] M) :
    @UniformContinuous _ _ (allStageUniformity (L := L)) (allStageUniformity (L := M))
      (allStageSuccessor action) := by
  let _ : ∀ (p : Nat.Primes) (j : Nat), UniformSpace (StageResidual (L := L) p j) := fun _ _ => ⊥
  let _ : ∀ (p : Nat.Primes) (j : Nat), UniformSpace (StageResidual (L := M) p j) := fun _ _ => ⊥
  let _ : ∀ p : Nat.Primes, UniformSpace ((j : Nat) → StageResidual (L := L) p j) :=
    fun p => Pi.uniformSpace (fun j => StageResidual (L := L) p j)
  let _ : ∀ p : Nat.Primes, UniformSpace ((j : Nat) → StageResidual (L := M) p j) :=
    fun p => Pi.uniformSpace (fun j => StageResidual (L := M) p j)
  let _ : UniformSpace (AllStageObservation L) := allStageUniformity
  let _ : UniformSpace (AllStageObservation M) := allStageUniformity
  change UniformContinuous (allStageSuccessor action)
  apply uniformContinuous_pi.mpr
  intro prime
  apply uniformContinuous_pi.mpr
  intro stage
  have atPrime : UniformContinuous (fun x : AllStageObservation L => x prime) :=
    Pi.uniformContinuous_proj _ prime
  have atStage : UniformContinuous (fun x : (j : Nat) → StageResidual (L := L) prime j => x stage) :=
    Pi.uniformContinuous_proj _ stage
  have quotient : UniformContinuous (stageMap prime stage action) :=
    uniformContinuous_iff_le_comap.mpr bot_le
  exact quotient.comp (atStage.comp atPrime)

theorem allStage_source_successor_uniformContinuous (action : L →ₗ[ℤ] M) :
    @UniformContinuous _ _ (allStageSourceUniformity (L := L)) (allStageSourceUniformity (L := M)) action := by
  let _ : UniformSpace (AllStageObservation L) := allStageUniformity
  let _ : UniformSpace (AllStageObservation M) := allStageUniformity
  let _ : UniformSpace L := allStageSourceUniformity
  apply uniformContinuous_comap'
  have source : UniformContinuous (allStageMap (L := L)) := uniformContinuous_comap
  have moved := (allStage_successor_uniformContinuous action).comp source
  have equation : (allStageSuccessor action : _ → _) ∘ allStageMap =
      (allStageMap (L := M) : _ → _) ∘ action :=
    funext (allStage_successor_source action)
  rwa [equation] at moved

private theorem allPrime_kernel_maps (action : L →ₗ[ℤ] M) :
    AllPrimeKernel (L := L) ≤ (AllPrimeKernel (L := M)).comap action := by
  intro value hidden
  apply (allStage_zero_iff_kernel (action value)).mp
  rw [← allStage_successor_source, (allStage_zero_iff_kernel value).mpr hidden, map_zero]

/-- The separated carrier advances with the same action and exact arithmetic fibre. -/
def allPrimeCoimageSuccessor (action : L →ₗ[ℤ] M) :
    AllPrimeFaithfulCoimage (L := L) →ₗ[ℤ] AllPrimeFaithfulCoimage (L := M) :=
  Submodule.mapQ (AllPrimeKernel (L := L)) (AllPrimeKernel (L := M)) action (allPrime_kernel_maps action)

theorem allPrime_coimage_successor_source (action : L →ₗ[ℤ] M) (value : L) :
    allPrimeCoimageSuccessor action ((AllPrimeKernel (L := L)).mkQ value) =
      (AllPrimeKernel (L := M)).mkQ (action value) := rfl

theorem allStage_successor_fibre (action : L →ₗ[ℤ] M) (left right : L) :
    allStageSuccessor action (allStageMap left) = allStageSuccessor action (allStageMap right) ↔
      ∀ p : Nat.Primes, ∀ j : Nat, ∃ divided : M, (p.1 : ℤ)^(j+1) • divided = action (left-right) := by
  rw [allStage_successor_source, allStage_successor_source, ← sub_eq_zero, ← map_sub, ← map_sub,
    allStage_zero_iff_kernel, allPrimeKernel_iff]

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
