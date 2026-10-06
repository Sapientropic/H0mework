import H0mework.Arithmetic.PrimeLeakage.SourceAllPrimeLeakage

/-!
# Zero-owned all-place Weil quadratic occurrence

The Euler-log coefficient, selected/reversal character reads, their faithful
primewise difference, and its positive quadratic are generated before
branching from the same zero/character/Müntz joint-state occurrence.  Every
character map in the payload consumes the stored integral graph orbit; closed
global maps appear only as root readback theorems.
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
namespace Occurrence

open ActionCofiber.RawEffect.AllPrimeCofinal
open ActionCofiber.RawEffect.AllPrimeLeakage
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open RootedAccountedUnfolding
open EulerDiagonal
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source

noncomputable section

def jointStateAnalyticOwner
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :=
  source.1.1.1.1.1

structure GeneratedZeroOwnedAllPrimeWeilQuadraticFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    Type 5 where
  private mk ::
  eulerFace : GeneratedEulerLogFaceAt (jointStateAnalyticOwner source)
  selectedCharacterMap : AllPrimeCurrent →ₗ[ℤ] ℂ
  reversalCharacterMap : AllPrimeCurrent →ₗ[ℤ] ℂ
  leakageMap : AllPrimeCurrent →ₗ[ℤ] PrimeLeakageCarrier
  weightedEnergy : AllPrimeCurrent → ℝ
  eulerFace_eq : eulerFace =
    GeneratedEulerLogFaceAt.generate (jointStateAnalyticOwner source)
  selectedCharacterMap_eq : selectedCharacterMap =
    allPrimeSelectedCharacterMapFromSource source
  reversalCharacterMap_eq : reversalCharacterMap =
    allPrimeReversalCharacterMapFromSource source
  leakageMap_eq : leakageMap =
    allPrimeCharacterLeakageMapFromSource source
  weightedEnergy_eq : weightedEnergy =
    eulerWeightedLeakageEnergyFromSource eulerFace source

def generateZeroOwnedAllPrimeWeilQuadraticFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    GeneratedZeroOwnedAllPrimeWeilQuadraticFaceAt
      observation nontrivial source := by
  let eulerFace :=
    GeneratedEulerLogFaceAt.generate (jointStateAnalyticOwner source)
  refine
    { eulerFace := eulerFace
      selectedCharacterMap :=
        allPrimeSelectedCharacterMapFromSource source
      reversalCharacterMap :=
        allPrimeReversalCharacterMapFromSource source
      leakageMap := allPrimeCharacterLeakageMapFromSource source
      weightedEnergy :=
        eulerWeightedLeakageEnergyFromSource eulerFace source
      eulerFace_eq := rfl
      selectedCharacterMap_eq := rfl
      reversalCharacterMap_eq := rfl
      leakageMap_eq := rfl
      weightedEnergy_eq := rfl }

abbrev ZeroOwnedAllPrimeWeilQuadraticPayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Σ source : ZeroOwnedJointStateModulePayload observation nontrivial,
    GeneratedZeroOwnedAllPrimeWeilQuadraticFaceAt
      observation nontrivial source

def zeroOwnedAllPrimeWeilQuadraticOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding
      (ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial) :=
  (zeroOwnedJointStateModuleOccurrence observation nontrivial).map fun source =>
    ⟨source,
      generateZeroOwnedAllPrimeWeilQuadraticFace
        observation nontrivial source⟩

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).map Sigma.fst =
      zeroOwnedJointStateModuleOccurrence observation nontrivial := by
  rw [zeroOwnedAllPrimeWeilQuadraticOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroOwnedJointStateModuleOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (((((((zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Prod.fst = seedOccurrence := by
  rw [zeroOwnedAllPrimeWeilQuadraticOccurrence_projects,
    zeroOwnedJointStateModuleOccurrence_projects,
    zeroOwnedCharacterMuntzCokernelOccurrence_projects_to_seed]

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_root_selectedCharacterMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.selectedCharacterMap =
        allPrimeSelectedCharacterMap observation nontrivial := by
  change allPrimeSelectedCharacterMapFromSource
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root = _
  exact allPrimeSelectedCharacterMapFromSource_root_eq
    observation nontrivial

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_root_reversalCharacterMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.reversalCharacterMap =
        allPrimeReversalCharacterMap observation nontrivial := by
  change allPrimeReversalCharacterMapFromSource
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root = _
  exact allPrimeReversalCharacterMapFromSource_root_eq
    observation nontrivial

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_root_leakageMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.leakageMap =
        allPrimeCharacterLeakageMap observation := by
  change allPrimeCharacterLeakageMapFromSource
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root = _
  exact allPrimeCharacterLeakageMapFromSource_root_eq
    observation nontrivial

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_root_weightedEnergy
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.weightedEnergy =
        allPrimeEulerWeightedLeakageEnergy observation := by
  change eulerWeightedLeakageEnergyFromSource
      (GeneratedEulerLogFaceAt.generate _)
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root = _
  funext current
  rw [eulerWeightedLeakageEnergyFromSource_root_eq,
    generatedEulerFaceWeightedLeakageEnergy_eq_allPrime]

theorem zeroOwnedAllPrimeWeilQuadraticOccurrence_root_single_zero_iff_fullRow
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial
      ).root.2.weightedEnergy (Finsupp.single prime 1) = 0 ↔
      generatedPrimeFullRowReadback observation prime = 0 := by
  rw [zeroOwnedAllPrimeWeilQuadraticOccurrence_root_weightedEnergy]
  exact allPrimeEulerWeightedLeakageEnergy_single_eq_zero_iff_fullRow
    observation prime

end
end Occurrence
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
