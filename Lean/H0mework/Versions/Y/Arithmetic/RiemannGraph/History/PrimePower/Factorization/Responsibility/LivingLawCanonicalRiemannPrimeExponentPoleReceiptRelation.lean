import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleRootEffectProjection
import H0mework.Foundation.Source.AdditiveTraceFold

/-!
# Receipt-rooted prime-exponent energy/vertical relation

The existing arithmetic certified-row occurrence is mapped directly to the
single dependent relation `retained = energy + vertical`.  This file adds no
recursive history and does not duplicate the installed phase/centered balance
row.
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
namespace History
namespace PrimePowerCurrent
namespace ReceiptRelation

open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalHistorySettlement
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure

noncomputable section

/-- The receipt index exposed by one framework-generated arithmetic cursor. -/
def scheduledConductorPrimePowerIndex (cursor : Nat) :
    ConductorPrimePowerIndex :=
  ⟨scheduledPrime cursor,
    ⟨scheduledExponent cursor, scheduledExponent_positive cursor⟩⟩

/-- Minimal dependent vocabulary.  The older phase/centered balance relation
remains in its installed effect history. -/
inductive PrimeExponentPoleReceiptRole
  | retained
  | energy
  | vertical
  deriving DecidableEq

abbrev PrimeExponentPoleReceiptRelation :=
  PrimeExponentPoleReceiptRole →₀ ℤ

def receiptRoleAtom (role : PrimeExponentPoleReceiptRole) :
    PrimeExponentPoleReceiptRelation :=
  Finsupp.single role 1

def retainedEnergyVerticalRelation : PrimeExponentPoleReceiptRelation :=
  receiptRoleAtom .retained - receiptRoleAtom .energy -
    receiptRoleAtom .vertical

def retainedEnergyVerticalPresentedEvent :
    PresentedRelationEventAt PrimeExponentPoleReceiptRole :=
  .relation retainedEnergyVerticalRelation

def receiptRoleValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) : PrimeExponentPoleReceiptRole → QRich.ClozelJPair
  | .retained => pairedPrimeExponentPoleBoundaryMellin observation nontrivial
      (scheduledConductorPrimePowerIndex cursor)
  | .energy => pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
      (scheduledConductorPrimePowerIndex cursor)
  | .vertical => pairedPrimeExponentPoleBoundaryVerticalTrace
      observation nontrivial (scheduledConductorPrimePowerIndex cursor)

def receiptRelationEvaluator
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    PrimeExponentPoleReceiptRelation →ₗ[ℤ] QRich.ClozelJPair :=
  (Finsupp.liftAddHom fun role =>
    AddMonoidHom.flip (smulAddHom ℤ QRich.ClozelJPair)
      (receiptRoleValue observation nontrivial cursor role)).toIntLinearMap

@[simp] theorem receiptRelationEvaluator_atom
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    receiptRelationEvaluator observation nontrivial cursor
        (receiptRoleAtom role) =
      receiptRoleValue observation nontrivial cursor role := by
  simp [receiptRelationEvaluator, receiptRoleAtom]

/-- The dependent relation is killed by the actual paired Mellin split. -/
theorem retainedEnergyVerticalRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    receiptRelationEvaluator observation nontrivial cursor
        retainedEnergyVerticalRelation = 0 := by
  rw [retainedEnergyVerticalRelation, map_sub, map_sub,
    receiptRelationEvaluator_atom, receiptRelationEvaluator_atom,
    receiptRelationEvaluator_atom]
  change pairedPrimeExponentPoleBoundaryMellin observation nontrivial
        (scheduledConductorPrimePowerIndex cursor) -
      pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
        (scheduledConductorPrimePowerIndex cursor) -
      pairedPrimeExponentPoleBoundaryVerticalTrace observation nontrivial
        (scheduledConductorPrimePowerIndex cursor) = 0
  rw [pairedPrimeExponentPoleBoundaryMellin_verticalSplit]
  module

/-- One dependent point over the exact certified arithmetic row.  Its extra
fields are generated coordinates, not caller-supplied relation data. -/
structure PrimeExponentPoleReceiptRelationPointAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) where
  private mk ::
  certifiedRow : FactorizationRoot × CertifiedLocalRowAt cursor
  index : ConductorPrimePowerIndex
  relationEvent : PresentedRelationEventAt PrimeExponentPoleReceiptRole
  index_eq : index = scheduledConductorPrimePowerIndex cursor
  relationEvent_eq : relationEvent = retainedEnergyVerticalPresentedEvent

def generateReceiptRelationPoint
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat)
    (certifiedRow : FactorizationRoot × CertifiedLocalRowAt cursor) :
    PrimeExponentPoleReceiptRelationPointAt observation nontrivial cursor :=
  ⟨certifiedRow, scheduledConductorPrimePowerIndex cursor,
    retainedEnergyVerticalPresentedEvent, rfl, rfl⟩

/-- No second history: this is a direct dependent map of the already generated
certified-row occurrence. -/
def primeExponentPoleReceiptRelationOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    RootedAccountedUnfolding
      (PrimeExponentPoleReceiptRelationPointAt
        observation nontrivial cursor) :=
  (certifiedRowOccurrence cursor).map
    (generateReceiptRelationPoint observation nontrivial cursor)

theorem primeExponentPoleReceiptRelationOccurrence_projects_certifiedRow
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    (primeExponentPoleReceiptRelationOccurrence
      observation nontrivial cursor).map
        PrimeExponentPoleReceiptRelationPointAt.certifiedRow =
      certifiedRowOccurrence cursor := by
  rw [primeExponentPoleReceiptRelationOccurrence,
    RootedAccountedUnfolding.map_map]
  change (certifiedRowOccurrence cursor).map id = certifiedRowOccurrence cursor
  exact RootedAccountedUnfolding.map_id _

def primeExponentPoleReceiptPresentedRelationOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    RootedAccountedUnfolding
      (PresentedRelationEventAt PrimeExponentPoleReceiptRole) :=
  (primeExponentPoleReceiptRelationOccurrence
    observation nontrivial cursor).map
      PrimeExponentPoleReceiptRelationPointAt.relationEvent

@[simp] theorem primeExponentPoleReceiptPresentedRelationOccurrence_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    (primeExponentPoleReceiptPresentedRelationOccurrence
      observation nontrivial cursor).root =
        retainedEnergyVerticalPresentedEvent := by
  rfl

theorem retainedEnergyVerticalPresentedEvent_mem_trace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    retainedEnergyVerticalPresentedEvent ∈
      (primeExponentPoleReceiptPresentedRelationOccurrence
        observation nontrivial cursor).trace := by
  rw [← primeExponentPoleReceiptPresentedRelationOccurrence_root]
  exact RootedAccountedUnfolding.root_mem_trace _

/-- Every node of this dependent occurrence carries the already evaluated
receipt relation; children contribute only by additive accumulation. -/
def receiptWholeOccurrenceNodeAlgebra
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    PresentedRelationEventAt PrimeExponentPoleReceiptRole →
      List QRich.ClozelJPair → QRich.ClozelJPair :=
  RootedAccountedUnfolding.additiveFoldAlgebra fun _event =>
    receiptRelationEvaluator observation nontrivial cursor
      retainedEnergyVerticalRelation

/-- The whole mapped occurrence has zero canonical evaluation.  This is the
existing additive trace fold, not a new recursive observer. -/
theorem receiptWholeOccurrenceFold_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    (primeExponentPoleReceiptPresentedRelationOccurrence
      observation nontrivial cursor).fold
        (receiptWholeOccurrenceNodeAlgebra
          observation nontrivial cursor) = 0 := by
  unfold receiptWholeOccurrenceNodeAlgebra
  rw [← RootedAccountedUnfolding.traceSum_eq_fold]
  simp [RootedAccountedUnfolding.traceSum,
    retainedEnergyVerticalRelation_evaluates_zero]

/-- Any whole-occurrence candidate respecting the same node algebra is the
canonical zero fold, by the existing `fold_unique`. -/
theorem receiptWholeOccurrenceCandidate_unique_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat)
    (candidate : RootedAccountedUnfolding
        (PresentedRelationEventAt PrimeExponentPoleReceiptRole) →
      QRich.ClozelJPair)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        receiptWholeOccurrenceNodeAlgebra observation nontrivial cursor origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate (primeExponentPoleReceiptPresentedRelationOccurrence
        observation nontrivial cursor) = 0 := by
  rw [RootedAccountedUnfolding.fold_unique
    (receiptWholeOccurrenceNodeAlgebra observation nontrivial cursor)
    candidate commutes]
  exact receiptWholeOccurrenceFold_eq_zero
    observation nontrivial cursor

theorem scheduledConductorPrimePowerIndex_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    scheduledConductorPrimePowerIndex (scheduleIndex prime exponent) =
      ⟨prime, ⟨exponent, positive⟩⟩ := by
  refine Sigma.ext (scheduledPrime_scheduleIndex prime exponent) ?_
  exact heq_of_eq (Subtype.ext
    (scheduledExponent_scheduleIndex prime exponent positive))

/-- Requested `(p,k>0)` is only a specialization of the generated cursor.
The retained value is the installed runtime field, while the energy/vertical
coordinates are literally the existing factor-boundary split. -/
theorem requestedScheduleIndex_reads_existing_split
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let cursor := scheduleIndex prime exponent
    let index : ConductorPrimePowerIndex :=
      ⟨prime, ⟨exponent, positive⟩⟩
    type_of% (requested_row_generated prime exponent positive) ∧
      (primeExponentPoleReceiptRelationOccurrence
        observation nontrivial cursor).root.index = index ∧
      receiptRoleValue observation nontrivial cursor .retained =
        (installedRuntimeEffectValueAt observation nontrivial
          (AllPlace.WeilQuadratic.PrimePower.Runtime.primePowerRuntimeStage
            prime exponent)).retained ∧
      receiptRoleValue observation nontrivial cursor .energy =
        pairedPrimeExponentPoleBoundaryRieszEnergy
          observation nontrivial index ∧
      receiptRoleValue observation nontrivial cursor .vertical =
        pairedPrimeExponentPoleBoundaryVerticalTrace
          observation nontrivial index ∧
      receiptRoleValue observation nontrivial cursor .retained =
        receiptRoleValue observation nontrivial cursor .energy +
          receiptRoleValue observation nontrivial cursor .vertical := by
  dsimp only
  have indexEq := scheduledConductorPrimePowerIndex_scheduleIndex
    prime exponent positive
  refine ⟨requested_row_generated prime exponent positive, ?_, ?_, ?_, ?_, ?_⟩
  · exact indexEq
  · change pairedPrimeExponentPoleBoundaryMellin observation nontrivial
        (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent)) = _
    rw [indexEq, pairedPrimeExponentPoleBoundaryMellin_eq_installedRetained,
      ← installedRuntimeEffectValueAt_retained_eq_jointIncidence]
  · change pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
        (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent)) = _
    rw [indexEq]
  · change pairedPrimeExponentPoleBoundaryVerticalTrace observation nontrivial
        (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent)) = _
    rw [indexEq]
  · change pairedPrimeExponentPoleBoundaryMellin observation nontrivial
        (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent)) =
      pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
          (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent)) +
        pairedPrimeExponentPoleBoundaryVerticalTrace observation nontrivial
          (scheduledConductorPrimePowerIndex (scheduleIndex prime exponent))
    exact pairedPrimeExponentPoleBoundaryMellin_verticalSplit
      observation nontrivial _

end
end ReceiptRelation
end PrimePowerCurrent
end History
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
