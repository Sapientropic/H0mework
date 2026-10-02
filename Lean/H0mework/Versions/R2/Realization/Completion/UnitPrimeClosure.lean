import Mathlib.Data.Nat.Pairing
import H0mework.Versions.R2.Arithmetic.EulerLocal.LandingSuccessor
import H0mework.Realization.Completion.HistorySettlement

/-!
# Root-generated canonical-unit prime-power cofinal closure

This arithmetic framework adapter consumes the domain's exact local
quotient-zero row and its one successor restriction square.  A numeric cursor
is framework-owned navigation only: each row is first regenerated as an
actual `RuntimePrimePowerFactorAt` and certified by the local
Euler/factorization producer.  Only then is it linearized into the common
presentation history.

`RootGeneratedCofinalHistoryAt` owns the schedule, relation/generator closure,
completion and same component.  The canonical quotient kernel owns range
membership and division roots; frozen rigidity owns residual zero.  No
completed table, global carrier, global finite-generation premise, division
root, fixedness, compactness, determinant or positive branch enters the
mouth.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerLocalLanding
open CanonicalUnitArithmeticFactorizationEulerLocalLandingSuccessor
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt

noncomputable section

inductive Generator
  | component (dualIndex : Fin 2)
  | quotientHistory (cursor : Nat) (dualIndex : Fin 2)
  | cursor (value : Nat)
  deriving DecidableEq

abbrev Event := PresentedRelationEventAt Generator

def scheduledCandidate (cursor : Nat) : Nat :=
  (Nat.unpair cursor).1

def scheduledPrime (cursor : Nat) : Nat.Primes :=
  if primeProof : Nat.Prime (scheduledCandidate cursor) then
    ⟨scheduledCandidate cursor, primeProof⟩
  else
    ⟨2, Nat.prime_two⟩

def scheduledExponent (cursor : Nat) : Nat :=
  (Nat.unpair cursor).2 + 1

theorem scheduledExponent_positive (cursor : Nat) :
    0 < scheduledExponent cursor := by
  unfold scheduledExponent
  omega

def scheduledFactor (cursor : Nat) :
    RuntimePrimePowerFactorAt (scheduledPrime cursor)
      (scheduledExponent cursor) :=
  RuntimePrimePowerFactorAt.generate
    (scheduledPrime cursor) (scheduledExponent cursor)
      (scheduledExponent_positive cursor)

abbrev FactorizationRoot :=
  Σ authority : RuntimeAuthority,
    GeneratedUnitFactorizationAt (authorityWholeHistory authority)

/-- Exact domain material consumed by one framework row.  The constructor is
private: quotient zero and successor preservation are calculated from the
same actual factorization/Euler occurrence. -/
structure CertifiedLocalRowAt (cursor : Nat) : Type where
  private mk ::
  quotientZero :
    quotientEvaluator (scheduledFactor cursor)
        (difference (scheduledFactor cursor))
        (scheduledPrime cursor) (scheduledExponent cursor) = 0
  successorDifference :
    carrierRestriction (scheduledFactor cursor)
        (difference (scheduledFactor cursor).advance) =
      difference (scheduledFactor cursor)
  successorQuotientSquare :
    quotientMap (carrierRestriction (scheduledFactor cursor)).toAddMonoidHom
        (scheduledPrime cursor) (scheduledExponent cursor)
        (quotientEvaluator (scheduledFactor cursor).advance
          (difference (scheduledFactor cursor).advance)
          (scheduledPrime cursor) (scheduledExponent cursor)) =
      quotientEvaluator (scheduledFactor cursor)
        (difference (scheduledFactor cursor))
        (scheduledPrime cursor) (scheduledExponent cursor)

namespace CertifiedLocalRowAt

def generate (cursor : Nat) : CertifiedLocalRowAt cursor :=
  ⟨difference_quotientZero (scheduledFactor cursor),
    carrierRestriction_difference (scheduledFactor cursor),
    quotientRestriction_difference (scheduledFactor cursor)⟩

end CertifiedLocalRowAt

/-- The certified row remains on the exact factorization occurrence that
generated its carrier, quotient-zero and successor square. -/
def certifiedRowOccurrence (cursor : Nat) :
    RootedAccountedUnfolding
      (FactorizationRoot × CertifiedLocalRowAt cursor) :=
  (factorizationOccurrence (scheduledFactor cursor).stage).map fun root =>
    (root, CertifiedLocalRowAt.generate cursor)

theorem certifiedRowOccurrence_projects_to_factorization
    (cursor : Nat) :
    (certifiedRowOccurrence cursor).map Prod.fst =
      factorizationOccurrence (scheduledFactor cursor).stage := by
  rw [certifiedRowOccurrence, RootedAccountedUnfolding.map_map]
  change (factorizationOccurrence (scheduledFactor cursor).stage).map id =
    factorizationOccurrence (scheduledFactor cursor).stage
  exact RootedAccountedUnfolding.map_id _

def componentDifference : Generator →₀ ℤ :=
  Finsupp.single (.component 0) 1 -
    Finsupp.single (.component 1) 1

def quotientHistoryDifference (cursor : Nat) : Generator →₀ ℤ :=
  Finsupp.single (.quotientHistory cursor 0) 1 -
    Finsupp.single (.quotientHistory cursor 1) 1

/-- Formal row corresponding to the actual local landing at this cursor. -/
def scheduledRelation (cursor : Nat) : Generator →₀ ℤ :=
  componentDifference -
    ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor : ℤ) •
      quotientHistoryDifference cursor

def scheduledRelationEvent (cursor : Nat) : Event :=
  .relation (scheduledRelation cursor)

def cursorKillEvent (cursor : Nat) : Event :=
  .relation (Finsupp.single (.cursor cursor) 1)

def cursorMarkerEvent (cursor : Nat) : Event :=
  .generator (.cursor cursor)

/-- Framework linearization occurs only after the exact local row and its
successor square have been generated. -/
def rowOccurrence (cursor : Nat) : RootedAccountedUnfolding Event :=
  (certifiedRowOccurrence cursor).map
    fun _certified => scheduledRelationEvent cursor

/-- A finite row patch has one relation root, one killed cursor bookkeeping
atom and exactly one open cursor leaf. -/
def rowPatch (cursor : Nat) : RootedAccountedUnfolding Event :=
  ((rowOccurrence cursor).advance
      (fun _event => RootedAccountedUnfolding.zero
        (cursorKillEvent cursor))).advance
    (fun _event => RootedAccountedUnfolding.zero
      (cursorMarkerEvent cursor))

@[simp] theorem rowOccurrence_frontier (cursor : Nat) :
    (rowOccurrence cursor).frontier = [scheduledRelationEvent cursor] :=
  rfl

@[simp] theorem zero_frontier (event : Event) :
    (RootedAccountedUnfolding.zero event).frontier = [event] := by
  unfold RootedAccountedUnfolding.zero RootedAccountedUnfolding.frontier
  rfl

@[simp] theorem rowPatch_frontier (cursor : Nat) :
    (rowPatch cursor).frontier = [cursorMarkerEvent cursor] := by
  unfold rowPatch
  rw [RootedAccountedUnfolding.frontier_advance,
    RootedAccountedUnfolding.frontier_advance]
  rw [zero_frontier]
  simp

@[simp] theorem rowPatch_root (cursor : Nat) :
    (rowPatch cursor).root = scheduledRelationEvent cursor :=
  rfl

def nextPatch : Event → RootedAccountedUnfolding Event
  | .generator (.cursor cursor) => rowPatch (cursor + 1)
  | event => RootedAccountedUnfolding.zero event

def rootOccurrence := factorizationOccurrence 0

def seedEventOccurrence : RootedAccountedUnfolding Event :=
  rowPatch 0

def continuationOccurrence : RootedAccountedUnfolding
    (Event → RootedAccountedUnfolding Event) :=
  rootOccurrence.map fun _root => nextPatch

def history : RootGeneratedCofinalHistoryAt rootOccurrence
    seedEventOccurrence continuationOccurrence :=
  RootGeneratedCofinalHistoryAt.generate

@[simp] theorem nextPatch_cursor (cursor : Nat) :
    nextPatch (cursorMarkerEvent cursor) = rowPatch (cursor + 1) :=
  rfl

/-- The framework-generated observation has exactly the current source
cursor as its open frontier. -/
theorem observation_frontier (stage : Nat) :
    (history.observation stage).frontier = [cursorMarkerEvent stage] := by
  induction stage with
  | zero => exact rowPatch_frontier 0
  | succ stage inductionHypothesis =>
      rw [history.observation_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      change (nextPatch (cursorMarkerEvent stage)).frontier =
        [cursorMarkerEvent (stage + 1)]
      rw [nextPatch_cursor, rowPatch_frontier]

private theorem frontier_mem_trace
    (occurrence : RootedAccountedUnfolding Event) :
    ∀ event, event ∈ occurrence.frontier → event ∈ occurrence.trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ event, event ∈ current.frontier → event ∈ current.trace)
    (motive_2 := fun branches =>
      ∀ event, event ∈ RootedAccountedUnfolding.frontierBranches branches →
        event ∈ RootedAccountedUnfolding.traceBranches branches)
    (fun root branches branchResult event event_mem => by
      cases branches with
      | nil => exact event_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root (branchResult event event_mem))
    (fun event event_mem => by
      change event ∈ ([] : List Event) at event_mem
      exact False.elim (List.not_mem_nil event_mem))
    (fun head tail headResult tailResult event event_mem => by
      change event ∈ head.frontier ++
        RootedAccountedUnfolding.frontierBranches tail at event_mem
      change event ∈ head.trace ++
        RootedAccountedUnfolding.traceBranches tail
      rw [List.mem_append] at event_mem ⊢
      cases event_mem with
      | inl inHead => exact Or.inl (headResult event inHead)
      | inr inTail => exact Or.inr (tailResult event inTail))
    occurrence

private theorem next_trace_mem_trace_advance
    (next : Event → RootedAccountedUnfolding Event)
    (occurrence : RootedAccountedUnfolding Event) :
    ∀ leaf, leaf ∈ occurrence.frontier →
      ∀ event, event ∈ (next leaf).trace →
        event ∈ (occurrence.advance next).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ leaf, leaf ∈ current.frontier →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ (current.advance next).trace)
    (motive_2 := fun branches =>
      ∀ leaf,
        leaf ∈ RootedAccountedUnfolding.frontierBranches branches →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ RootedAccountedUnfolding.traceBranches
            (RootedAccountedUnfolding.advanceBranches next branches))
    (fun root branches branchResult leaf leaf_mem event event_mem => by
      cases branches with
      | nil =>
          change leaf ∈ [root] at leaf_mem
          have leaf_eq : leaf = root := by simpa using leaf_mem
          subst leaf
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.nil : AccountedBranches Event)).advance next =
                RootedAccountedUnfolding.occur root
                  (AccountedBranches.singleton (next root)) from rfl]
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.singleton (next root))).trace =
                root :: (next root).trace by
            simp [RootedAccountedUnfolding.trace,
              AccountedBranches.singleton]]
          change event ∈ root :: (next root).trace
          exact List.mem_cons_of_mem root event_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root
            (branchResult leaf leaf_mem event event_mem))
    (fun leaf leaf_mem event event_mem => by
      change leaf ∈ ([] : List Event) at leaf_mem
      exact False.elim (List.not_mem_nil leaf_mem))
    (fun head tail headResult tailResult leaf leaf_mem event event_mem => by
      change leaf ∈ head.frontier ++
        RootedAccountedUnfolding.frontierBranches tail at leaf_mem
      change event ∈ (head.advance next).trace ++
        RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.advanceBranches next tail)
      rw [List.mem_append] at leaf_mem ⊢
      cases leaf_mem with
      | inl inHead => exact Or.inl (headResult leaf inHead event event_mem)
      | inr inTail => exact Or.inr (tailResult leaf inTail event event_mem))
    occurrence

theorem scheduledRelationEvent_mem_observation_trace (cursor : Nat) :
    scheduledRelationEvent cursor ∈ (history.observation cursor).trace := by
  induction cursor with
  | zero =>
      have rootMem := RootedAccountedUnfolding.root_mem_trace
        (history.observation 0)
      rw [show (history.observation 0).root =
        scheduledRelationEvent 0 from rfl] at rootMem
      exact rootMem
  | succ cursor inductionHypothesis =>
      rw [history.observation_succ]
      apply next_trace_mem_trace_advance
        (next := history.actualContinuation)
        (leaf := cursorMarkerEvent cursor)
      · rw [observation_frontier]
        simp
      · change scheduledRelationEvent (cursor + 1) ∈
          (nextPatch (cursorMarkerEvent cursor)).trace
        rw [nextPatch_cursor]
        have rootMem := RootedAccountedUnfolding.root_mem_trace
          (rowPatch (cursor + 1))
        simpa [rowPatch_root] using rootMem

theorem scheduledRelationEvent_mem_observedEvents (cursor : Nat) :
    scheduledRelationEvent cursor ∈ history.observedEvents cursor := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap]
  refine ⟨cursor, by simp, ?_⟩
  exact scheduledRelationEvent_mem_observation_trace cursor

theorem scheduledRelation_mem_relationStage (cursor : Nat) :
    scheduledRelation cursor ∈ history.relationStage cursor := by
  apply Submodule.subset_span
  exact scheduledRelationEvent_mem_observedEvents cursor

theorem scheduledRelation_mem_relationClosure (cursor : Nat) :
    scheduledRelation cursor ∈ history.relationClosure :=
  history.relationStage_le_closure cursor
    (scheduledRelation_mem_relationStage cursor)

theorem event_support_subset_generatorSupport
    {stage : Nat} {event : Event}
    (event_mem : event ∈ history.observedEvents stage) :
    (event.support : Set Generator) ⊆ history.generatorSupport stage := by
  intro generator generator_mem
  rw [RootGeneratedCofinalHistoryAt.generatorSupport]
  have inFinset : generator ∈
      ((history.observedEvents stage).flatMap
        (fun current => current.support.toList)).toFinset := by
    rw [List.mem_toFinset, List.mem_flatMap]
    exact ⟨event, event_mem, by simpa using generator_mem⟩
  simpa using inFinset

theorem component_mem_generatorSupport (cursor : Nat)
    (dualIndex : Fin 2) :
    Generator.component dualIndex ∈ history.generatorSupport cursor := by
  apply event_support_subset_generatorSupport
    (scheduledRelationEvent_mem_observedEvents cursor)
  change Generator.component dualIndex ∈ (scheduledRelation cursor).support
  rw [Finsupp.mem_support_iff]
  fin_cases dualIndex <;>
    simp [scheduledRelation, componentDifference,
      quotientHistoryDifference]

theorem quotientHistory_mem_generatorSupport (cursor : Nat)
    (dualIndex : Fin 2) :
    Generator.quotientHistory cursor dualIndex ∈
      history.generatorSupport cursor := by
  apply event_support_subset_generatorSupport
    (scheduledRelationEvent_mem_observedEvents cursor)
  change Generator.quotientHistory cursor dualIndex ∈
    (scheduledRelation cursor).support
  rw [Finsupp.mem_support_iff]
  have primePowerNe :
      (((scheduledPrime cursor : Nat) ^ scheduledExponent cursor : Nat) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (scheduledExponent cursor)
      (scheduledPrime cursor).property.ne_zero
  fin_cases dualIndex
  · change scheduledRelation cursor
        (.quotientHistory cursor (0 : Fin 2)) ≠ 0
    have coefficient :
        scheduledRelation cursor (.quotientHistory cursor 0) =
          -(((scheduledPrime cursor : Nat) ^
            scheduledExponent cursor : Nat) : ℤ) := by
      simp [scheduledRelation, componentDifference,
        quotientHistoryDifference]
    rw [coefficient]
    exact neg_ne_zero.mpr primePowerNe
  · change scheduledRelation cursor
        (.quotientHistory cursor (1 : Fin 2)) ≠ 0
    have coefficient :
        scheduledRelation cursor (.quotientHistory cursor 1) =
          (((scheduledPrime cursor : Nat) ^
            scheduledExponent cursor : Nat) : ℤ) := by
      simp [scheduledRelation, componentDifference,
        quotientHistoryDifference]
    rw [coefficient]
    exact primePowerNe

def componentDifferenceStage (cursor : Nat) :
    history.generatorStage cursor := by
  refine ⟨componentDifference, ?_⟩
  apply Submodule.sub_mem
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (component_mem_generatorSupport cursor 0)
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (component_mem_generatorSupport cursor 1)

def quotientHistoryDifferenceStage (cursor : Nat) :
    history.generatorStage cursor := by
  refine ⟨quotientHistoryDifference cursor, ?_⟩
  apply Submodule.sub_mem
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (quotientHistory_mem_generatorSupport cursor 0)
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (quotientHistory_mem_generatorSupport cursor 1)

def presentedComponentAt (cursor : Nat) : history.CompletionCarrier :=
  history.stageGeneratorToCompletion cursor (componentDifferenceStage cursor)

def presentedGlobalComponent : history.CompletionCarrier :=
  presentedComponentAt 0

def presentedQuotientHistoryRoot (cursor : Nat) : history.CompletionCarrier :=
  history.stageGeneratorToCompletion cursor
    (quotientHistoryDifferenceStage cursor)

theorem presentedComponentAt_eq_global (cursor : Nat) :
    presentedComponentAt cursor = presentedGlobalComponent := by
  unfold presentedComponentAt presentedGlobalComponent
    RootGeneratedCofinalHistoryAt.stageGeneratorToCompletion
    RootGeneratedCofinalHistoryAt.completionProjection
    RootGeneratedCofinalHistoryAt.stageGeneratorToClosure
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

def scheduledRelationInGeneratorStage (cursor : Nat) :
    history.relationInGeneratorStage cursor :=
  ⟨⟨scheduledRelation cursor,
      history.relationStage_le_generatorStage cursor
        (scheduledRelation_mem_relationStage cursor)⟩,
    scheduledRelation_mem_relationStage cursor⟩

theorem scheduledRelation_mapsToZero (cursor : Nat) :
    history.stageGeneratorToCompletion cursor
        (scheduledRelationInGeneratorStage cursor).1 = 0 := by
  exact LinearMap.mem_ker.mp
    (history.stageRelationInGenerator_le_kernel cursor
      (scheduledRelationInGeneratorStage cursor).2)

theorem scheduled_primePower_landing (cursor : Nat) :
    ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) •
        presentedQuotientHistoryRoot cursor = presentedGlobalComponent := by
  have relationZero := scheduledRelation_mapsToZero cursor
  change presentedComponentAt cursor -
      ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) •
        presentedQuotientHistoryRoot cursor = 0 at relationZero
  rw [sub_eq_zero] at relationZero
  rw [← presentedComponentAt_eq_global cursor]
  exact relationZero.symm

def scheduleIndex (prime : Nat.Primes) (exponent : Nat) : Nat :=
  Nat.pair (prime : Nat) (exponent - 1)

@[simp] theorem scheduledCandidate_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) :
    scheduledCandidate (scheduleIndex prime exponent) = prime := by
  simp [scheduledCandidate, scheduleIndex]

@[simp] theorem scheduledPrime_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) :
    scheduledPrime (scheduleIndex prime exponent) = prime := by
  apply Subtype.ext
  simp [scheduledPrime, scheduledCandidate_scheduleIndex,
    prime.property]

@[simp] theorem scheduledExponent_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    scheduledExponent (scheduleIndex prime exponent) = exponent := by
  simp [scheduledExponent, scheduleIndex]
  omega

/-- Every requested positive prime power is reached by a concrete generated
cursor, with its authority still supplied by the actual factorization row. -/
theorem requested_row_generated
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let cursor := scheduleIndex prime exponent
    (history.observation cursor).frontier = [cursorMarkerEvent cursor] ∧
      scheduledPrime cursor = prime ∧
      scheduledExponent cursor = exponent ∧
      factorialHistory
          (runtimeWholeHistory (scheduledFactor cursor).stage) =
        (primePowerHistory (scheduledFactor cursor).primeIndex
          (scheduledFactor cursor).exponentIndex).joint
        (quotientHistory (scheduledFactor cursor).primeIndex
          (scheduledFactor cursor).exponentIndex) ∧
      CanonicalUnitArithmeticFactorizationEulerLocalLanding.quotientEvaluator
          (scheduledFactor cursor)
          (CanonicalUnitArithmeticFactorizationEulerLocalLanding.difference
            (scheduledFactor cursor))
          (scheduledPrime cursor) (scheduledExponent cursor) = 0 := by
  dsimp only
  refine ⟨observation_frontier _, scheduledPrime_scheduleIndex _ _,
    scheduledExponent_scheduleIndex _ _ positive, ?_⟩
  have localLanding :=
    localLanding_preserves_actual_factorization_and_fullEuler
      (scheduledFactor (scheduleIndex prime exponent))
  have quotientZero := difference_quotientZero
    (scheduledFactor (scheduleIndex prime exponent))
  exact ⟨localLanding.1, quotientZero⟩

def requestedPresentedDivisionRoot
    (prime : Nat.Primes) (exponent : Nat) : history.CompletionCarrier :=
  presentedQuotientHistoryRoot (scheduleIndex prime exponent)

theorem requested_presented_primePower_landing
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (prime : Nat) ^ exponent •
        requestedPresentedDivisionRoot prime exponent =
      presentedGlobalComponent := by
  unfold requestedPresentedDivisionRoot
  have landing := scheduled_primePower_landing
    (scheduleIndex prime exponent)
  simpa only [scheduledPrime_scheduleIndex,
    scheduledExponent_scheduleIndex prime exponent positive] using landing

def presentedQuotientEvaluator :
    history.CompletionCarrier →
      PrimePowerQuotientEvaluation.State history.CompletionCarrier :=
  PrimePowerQuotientEvaluation.evaluator history.CompletionCarrier

theorem presentedGlobalComponent_quotientZero
    (prime : Nat.Primes) (exponent : Nat) :
    presentedQuotientEvaluator presentedGlobalComponent prime exponent = 0 := by
  unfold presentedQuotientEvaluator
  apply (QuotientAddGroup.eq_zero_iff presentedGlobalComponent).2
  cases exponent with
  | zero =>
      exact ⟨presentedGlobalComponent, by simp⟩
  | succ exponent =>
      exact ⟨requestedPresentedDivisionRoot prime (exponent + 1),
        requested_presented_primePower_landing prime (exponent + 1) (by omega)⟩

theorem presentedGlobalComponent_evaluatorZero :
    presentedQuotientEvaluator presentedGlobalComponent = 0 := by
  funext prime exponent
  exact presentedGlobalComponent_quotientZero prime exponent

/-- The framework quotient kernel re-extracts an actual root from the
generated whole-family quotient zero. -/
def frameworkDivisionRoot
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    { root : history.CompletionCarrier //
      (prime : Nat) ^ exponent • root = presentedGlobalComponent } :=
  PrimePowerQuotientEvaluation.divisionRoot history.CompletionCarrier
    presentedGlobalComponent presentedGlobalComponent_evaluatorZero
      prime exponent positive

theorem frameworkDivisionRoot_landing
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (prime : Nat) ^ exponent •
        (frameworkDivisionRoot prime exponent positive).1 =
      presentedGlobalComponent :=
  (frameworkDivisionRoot prime exponent positive).2

set_option backward.isDefEq.respectTransparency false in
theorem mappedPresentedComponent_primePowerDivisible
    {G : Type*} [AddCommGroup G]
    (map : history.CompletionCarrier →+ G)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    ∃ root : G,
      (prime : Nat) ^ exponent • root = map presentedGlobalComponent := by
  refine ⟨map (frameworkDivisionRoot prime exponent positive), ?_⟩
  calc
    (prime : Nat) ^ exponent •
        map (frameworkDivisionRoot prime exponent positive).1 =
      map ((prime : Nat) ^ exponent •
        (frameworkDivisionRoot prime exponent positive).1) :=
      (map.map_nsmul _ _).symm
    _ = map presentedGlobalComponent := by
      rw [frameworkDivisionRoot_landing]

/-- Any framework-generated finitely generated realization of the presented
component is forced to kill it by frozen rigidity.  Its realization map must
be generated downstream from the certified local evaluator arrows and
successor squares; it is not a new domain premise. -/
theorem mappedPresentedComponent_eq_zero
    {G : Type*} [AddCommGroup G] (finiteGenerated : AddGroup.FG G)
    (map : history.CompletionCarrier →+ G) :
    map presentedGlobalComponent = 0 :=
  FinitelyGeneratedPrimePowerRigidity.eq_zero_of_prime_power_divisible
    finiteGenerated (map presentedGlobalComponent)
      (fun prime exponent positive =>
        mappedPresentedComponent_primePowerDivisible
          map prime exponent positive)

set_option linter.style.haveILetI false in
theorem completionFG_of_compactAt (stage : Nat)
    (compact : history.CompactAt stage) :
    AddGroup.FG history.CompletionCarrier := by
  have presentedEpi : history.PresentedEpiAt stage :=
    (history.compactAt_iff_presentedEpi stage).mp compact
  have generatorSurjective :
      Function.Surjective (history.stageGeneratorToCompletion stage) :=
    (history.stageGeneratorToCompletion_surjective_iff_presentedEpi
      stage).mpr presentedEpi
  let supportSet : Set Generator := history.generatorSupport stage
  let supportBasis : Module.Basis supportSet ℤ (supportSet →₀ ℤ) :=
    Finsupp.basisSingleOne
  let generatorBasis : Module.Basis supportSet ℤ
      (history.generatorStage stage) :=
    supportBasis.map (Finsupp.supportedEquivFinsupp supportSet).symm
  letI : Module.Finite ℤ (history.generatorStage stage) :=
    Module.Finite.of_basis generatorBasis
  letI : Module.Finite ℤ history.CompletionCarrier :=
    Module.Finite.of_surjective
      (history.stageGeneratorToCompletion stage) generatorSurjective
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

def compactQuotientFace (stage : Nat) (compact : history.CompactAt stage) :
    RootGeneratedPrimePowerQuotientEvaluationAt history.CompletionCarrier
      history.root (completionFG_of_compactAt stage compact) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate
    history.CompletionCarrier

def compactRigidityFace (stage : Nat) (compact : history.CompactAt stage) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      (compactQuotientFace stage compact).dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem presentedGlobalComponent_eq_zero_of_compactAt (stage : Nat)
    (compact : history.CompactAt stage) :
    presentedGlobalComponent = 0 := by
  apply (compactRigidityFace stage compact
    ).evaluator_eq_zero_implies_element_zero
    presentedGlobalComponent
  change RootGeneratedPrimePowerQuotientEvaluationAt.accountedEvaluator
      (G := history.CompletionCarrier) (compactQuotientFace stage compact)
        presentedGlobalComponent = 0
  rw [RootGeneratedPrimePowerQuotientEvaluationAt.accountedEvaluator_eq_canonical]
  exact presentedGlobalComponent_evaluatorZero

abbrev PresentedRigidityOutcome :=
  Sum (PLift (presentedGlobalComponent = 0))
    (PersistentPresentedResidualObstructionAt history)

/-- Caller-free composition of cofinal settlement and frozen rigidity. -/
noncomputable def settlePresentedRigidity : PresentedRigidityOutcome := by
  cases settlement : history.settle with
  | inl positive =>
      exact Sum.inl ⟨presentedGlobalComponent_eq_zero_of_compactAt
        positive.1.index positive.1.residualVanishes⟩
  | inr obstruction => exact Sum.inr obstruction

/-- Framework-owned total disposition of the generated presentation.  A
positive compact branch would generate finite presentation/perfectness;
otherwise the same history returns its persistent presented residual. -/
noncomputable def presentedSettlement := history.settle

theorem presentedSettlement_exhaustive :
    (∃ stage, history.CompactAt stage) ∨
      (∀ stage, ¬ history.CompactAt stage) :=
  history.settlement_exhaustive

theorem history_preserves_root_and_source_continuation :
    history.root = rootOccurrence ∧
      history.seed = seedEventOccurrence ∧
      history.actualContinuation = nextPatch := by
  exact history.preserves_actual_rooted_pro_occurrence

end
end RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
