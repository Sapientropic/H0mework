import H0mework.Arithmetic.PrimeLeakage.PrimePowerEulerQuadratic

/-!
# Zero-owned prime-power Weil boundary occurrence

An actual arithmetic prime-power receipt and one paired-runtime source
boundary are installed as a dependent face of the source-owned Euler--Weil
occurrence.  The face records only generated reads and their defining
equalities; vanishing, residual, critical-line, and RH data are absent.
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
namespace WeilQuadratic
namespace PrimePower
namespace Occurrence

open CanonicalUnitArithmeticFactorizationOccurrence
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open RootedAccountedUnfolding
open SourceGeneratedIntegralCharacterGroupRing
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Quadratic
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Source

noncomputable section

structure GeneratedZeroOwnedPrimePowerWeilBoundaryFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent)
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload
      observation nontrivial) : Type 5 where
  private mk ::
  actualFactor : RuntimePrimePowerFactorAt prime exponent
  actualReceipt : type_of%
    (primePowerRuntime_actualReceipt prime exponent positive)
  boundaryState : PairedOmegaJointRelationCarrier
  integralRead : IntegralScaleCarrier
  coherentRead : JointGraphTarget × JointGraphTarget
  selectedRead : ℂ
  reversalRead : ℂ
  eulerWeight : ℝ
  quadraticCoordinate : ℝ
  actualFactor_eq : actualFactor =
    RuntimePrimePowerFactorAt.generate prime exponent positive
  boundaryState_eq : boundaryState =
    primePowerBoundaryStateFromSource source prime exponent
  integralRead_eq : integralRead =
    primePowerBoundaryIntegralReadFromSource source prime exponent
  coherentRead_eq : coherentRead =
    primePowerBoundaryCoherentReadFromSource source prime exponent
  selectedRead_eq : selectedRead =
    primePowerSelectedCharacterReadFromSource source prime exponent
  reversalRead_eq : reversalRead =
    primePowerReversalCharacterReadFromSource source prime exponent
  eulerWeight_eq : eulerWeight =
    primePowerEulerWeightFromSource source prime exponent
  quadraticCoordinate_eq : quadraticCoordinate =
    primePowerEulerWeightedQuadraticFromSource source prime exponent

def generateZeroOwnedPrimePowerWeilBoundaryFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent)
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload
      observation nontrivial) :
    GeneratedZeroOwnedPrimePowerWeilBoundaryFaceAt
      observation nontrivial prime exponent positive source :=
  { actualFactor :=
      RuntimePrimePowerFactorAt.generate prime exponent positive
    actualReceipt :=
      primePowerRuntime_actualReceipt prime exponent positive
    boundaryState :=
      primePowerBoundaryStateFromSource source prime exponent
    integralRead :=
      primePowerBoundaryIntegralReadFromSource source prime exponent
    coherentRead :=
      primePowerBoundaryCoherentReadFromSource source prime exponent
    selectedRead :=
      primePowerSelectedCharacterReadFromSource source prime exponent
    reversalRead :=
      primePowerReversalCharacterReadFromSource source prime exponent
    eulerWeight :=
      primePowerEulerWeightFromSource source prime exponent
    quadraticCoordinate :=
      primePowerEulerWeightedQuadraticFromSource source prime exponent
    actualFactor_eq := rfl
    boundaryState_eq := rfl
    integralRead_eq := rfl
    coherentRead_eq := rfl
    selectedRead_eq := rfl
    reversalRead_eq := rfl
    eulerWeight_eq := rfl
    quadraticCoordinate_eq := rfl }

abbrev ZeroOwnedPrimePowerWeilBoundaryPayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :=
  Σ source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial,
    GeneratedZeroOwnedPrimePowerWeilBoundaryFaceAt
      observation nontrivial prime exponent positive source

def zeroOwnedPrimePowerWeilBoundaryOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    RootedAccountedUnfolding
      (ZeroOwnedPrimePowerWeilBoundaryPayload
        observation nontrivial prime exponent positive) :=
  (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).map
    fun source =>
      ⟨source, generateZeroOwnedPrimePowerWeilBoundaryFace
        observation nontrivial prime exponent positive source⟩

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).map Sigma.fst =
        zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial := by
  rw [zeroOwnedPrimePowerWeilBoundaryOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroOwnedAllPrimeWeilQuadraticOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    ((((((((zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Prod.fst =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [zeroOwnedPrimePowerWeilBoundaryOccurrence_projects,
    zeroOwnedAllPrimeWeilQuadraticOccurrence_projects_to_seed]

end
end Occurrence
end PrimePower
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
