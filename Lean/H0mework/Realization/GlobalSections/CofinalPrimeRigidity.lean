import Mathlib.Data.Nat.Pairing
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Cofinal.CoverageResidual

/-!
# Cofinal restriction-to-seed prime-power rigidity

This arithmetic framework kernel consumes one source-local seed occurrence
and one occurrence-indexed successor law.  At a current state the domain
supplies only:

* one component in the local carrier;
* its canonical quotient-zero row at the framework-scheduled prime power;
* one successor restriction preserving the component.

The framework recursively generates the stage history and its dependent
table.  It then extracts each local division root from quotient zero,
iterates the generated successor restrictions back to the seed carrier,
covers every positive prime power by its canonical schedule, assembles the
whole quotient evaluator zero there, and invokes frozen prime-power rigidity.

No `Nat`-indexed carrier/evaluator table, division root, all-prime family,
iterated restriction, global carrier, global finite-generation premise,
residual zero, equivalence or fixedness is accepted from the domain mouth.
The sole finite-generation input belongs to the seed finite presentation.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPrimePowerRestrictionRigidity

open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open CofinalCoverageResidualTower
open CofinalCoverageResidualTower.RootGeneratedCofinalCoverageResidualTowerAt
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u w

def scheduledCode (cursor : Nat) : Nat :=
  (Nat.unpair cursor).1

/-- Nested pairing makes every prime-power code recur cofinally: the outer
right coordinate is free authority time, not arithmetic data. -/
def scheduledCandidate (cursor : Nat) : Nat :=
  (Nat.unpair (scheduledCode cursor)).1

def scheduledPrime (cursor : Nat) : Nat.Primes :=
  if primeProof : Nat.Prime (scheduledCandidate cursor) then
    ⟨scheduledCandidate cursor, primeProof⟩
  else
    ⟨2, Nat.prime_two⟩

def scheduledExponent (cursor : Nat) : Nat :=
  (Nat.unpair (scheduledCode cursor)).2 + 1

theorem scheduledExponent_positive (cursor : Nat) :
    0 < scheduledExponent cursor := by
  unfold scheduledExponent
  omega

def scheduleIndexAfter
    (prime : Nat.Primes) (exponent lower : Nat) : Nat :=
  Nat.pair (Nat.pair (prime : Nat) (exponent - 1)) lower

def scheduleIndex (prime : Nat.Primes) (exponent : Nat) : Nat :=
  scheduleIndexAfter prime exponent 0

@[simp] theorem scheduledCandidate_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) :
    scheduledCandidate (scheduleIndex prime exponent) = prime := by
  simp [scheduledCandidate, scheduledCode, scheduleIndex,
    scheduleIndexAfter]

@[simp] theorem scheduledPrime_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) :
    scheduledPrime (scheduleIndex prime exponent) = prime := by
  apply Subtype.ext
  simp [scheduledPrime, scheduledCandidate_scheduleIndex,
    prime.property]

@[simp] theorem scheduledExponent_scheduleIndex
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    scheduledExponent (scheduleIndex prime exponent) = exponent := by
  simp [scheduledExponent, scheduledCode, scheduleIndex,
    scheduleIndexAfter]
  omega

@[simp] theorem scheduledPrime_scheduleIndexAfter
    (prime : Nat.Primes) (exponent lower : Nat) :
    scheduledPrime (scheduleIndexAfter prime exponent lower) = prime := by
  apply Subtype.ext
  simp [scheduledPrime, scheduledCandidate, scheduledCode,
    scheduleIndexAfter, prime.property]

@[simp] theorem scheduledExponent_scheduleIndexAfter
    (prime : Nat.Primes) (exponent lower : Nat)
    (positive : 0 < exponent) :
    scheduledExponent (scheduleIndexAfter prime exponent lower) =
      exponent := by
  simp [scheduledExponent, scheduledCode, scheduleIndexAfter]
  omega

theorem lower_le_scheduleIndexAfter
    (prime : Nat.Primes) (exponent lower : Nat) :
    lower ≤ scheduleIndexAfter prime exponent lower :=
  Nat.right_le_pair _ _

/-- One local source law over a domain state.  `next` is applied only to the
current generated state; it is not a completed future table. -/
structure PrimePowerRestrictionLocalProcessAt (State : Type u) where
  cursor : State → Nat
  Carrier : State → AddCommGrpCat.{u}
  component : (state : State) → Carrier state
  finiteGenerated : ∀ state, AddGroup.FG (Carrier state)
  quotientZero : ∀ state,
    PrimePowerQuotientEvaluation.evaluator (Carrier state) (component state)
        (scheduledPrime (cursor state)) (scheduledExponent (cursor state)) = 0
  next : State → State
  cursor_next : ∀ state, cursor (next state) = cursor state + 1
  restriction : (state : State) → Carrier (next state) →+ Carrier state
  component_next : ∀ state,
    restriction state (component (next state)) = component state

/-- Framework-private generated readout.  Its constructor is unavailable to
domain callers; only the seed/successor history below may materialize it. -/
structure CofinalPrimePowerRestrictionTableAt where
  private mk ::
  Carrier : Nat → AddCommGrpCat.{u}
  restriction : (stage : Nat) → Carrier (stage + 1) →+ Carrier stage
  component : (stage : Nat) → Carrier stage
  finiteGenerated : ∀ stage, AddGroup.FG (Carrier stage)
  component_succ : ∀ stage,
    restriction stage (component (stage + 1)) = component stage
  quotientZero : ∀ stage,
    PrimePowerQuotientEvaluation.evaluator (Carrier stage) (component stage)
        (scheduledPrime stage) (scheduledExponent stage) = 0

/-- Root-owned seed plus one local successor law.  The law is installed on
the same occurrence tree as the seed; no stage family occurs in the mouth. -/
structure RootGeneratedCofinalPrimePowerRestrictionHistoryAt
    {Root : Type w} {State : Type u}
    (seedOccurrence : RootedAccountedUnfolding (Root × State))
    (successorOccurrence : RootedAccountedUnfolding
      (Root × PrimePowerRestrictionLocalProcessAt State))
    (_projects : successorOccurrence.map Prod.fst =
      seedOccurrence.map Prod.fst)
    (_seedCursor : successorOccurrence.root.2.cursor
      seedOccurrence.root.2 = 0) : Type (max u w) where
  private mk ::

namespace RootGeneratedCofinalPrimePowerRestrictionHistoryAt

variable {Root : Type w} {State : Type u}
variable {seedOccurrence : RootedAccountedUnfolding (Root × State)}
variable {successorOccurrence : RootedAccountedUnfolding
  (Root × PrimePowerRestrictionLocalProcessAt State)}
variable {projects : successorOccurrence.map Prod.fst =
  seedOccurrence.map Prod.fst}
variable {seedCursor : successorOccurrence.root.2.cursor
  seedOccurrence.root.2 = 0}

def generate : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
    seedOccurrence successorOccurrence projects seedCursor :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootedAccountedUnfolding Root :=
  seedOccurrence.map Prod.fst

def actualProcess
    (_face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    PrimePowerRestrictionLocalProcessAt State :=
  successorOccurrence.root.2

def seedState
    (_face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) : State :=
  seedOccurrence.root.2

/-- Recursive execution of the one local successor. -/
def advanceFrom (process : PrimePowerRestrictionLocalProcessAt State) :
    Nat → State → State
  | 0, state => state
  | stage + 1, state => process.next (advanceFrom process stage state)

def stageState
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) : State :=
  advanceFrom face.actualProcess stage face.seedState

@[simp] theorem stageState_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.stageState 0 = face.seedState :=
  rfl

@[simp] theorem stageState_succ
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.stageState (stage + 1) =
      face.actualProcess.next (face.stageState stage) :=
  rfl

/-- The framework schedule index is generated by recursive execution. -/
theorem stageCursor
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    ∀ stage, face.actualProcess.cursor (face.stageState stage) = stage
  | 0 => seedCursor
  | stage + 1 => by
      rw [face.stageState_succ,
        face.actualProcess.cursor_next,
        face.stageCursor stage]

/-- Every finite observation is calculated from the same seed occurrence
and the installed local successor, rather than read from a submitted table. -/
def stageOccurrence
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) : RootedAccountedUnfolding (Root × State) :=
  seedOccurrence.map fun point =>
    (point.1, advanceFrom face.actualProcess stage point.2)

theorem stageOccurrence_projects_to_root
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    (face.stageOccurrence stage).map Prod.fst = face.root := by
  unfold stageOccurrence root
  rw [RootedAccountedUnfolding.map_map]
  rfl

@[simp] theorem stageOccurrence_root_state
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    (face.stageOccurrence stage).root.2 = face.stageState stage :=
  by
    unfold stageOccurrence stageState seedState
    rw [RootedAccountedUnfolding.root_map]

/-- The completed table is now a framework-generated readout of the local
history. -/
def generatedTable
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    CofinalPrimePowerRestrictionTableAt where
  Carrier stage := face.actualProcess.Carrier (face.stageState stage)
  restriction stage :=
    face.actualProcess.restriction (face.stageState stage)
  component stage :=
    face.actualProcess.component (face.stageState stage)
  finiteGenerated stage :=
    face.actualProcess.finiteGenerated (face.stageState stage)
  component_succ stage :=
    face.actualProcess.component_next (face.stageState stage)
  quotientZero stage := by
    have localZero :=
      face.actualProcess.quotientZero (face.stageState stage)
    rw [face.stageCursor stage] at localZero
    exact localZero

def generatedTableOccurrence
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootedAccountedUnfolding
      (Root × CofinalPrimePowerRestrictionTableAt) :=
  seedOccurrence.map fun point => (point.1, face.generatedTable)

@[simp] theorem generatedTableOccurrence_root_table
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.generatedTableOccurrence.root.2 = face.generatedTable := by
  unfold generatedTableOccurrence
  rw [RootedAccountedUnfolding.root_map]

@[simp] theorem generatedTable_carrier_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.generatedTable.Carrier 0 =
      face.actualProcess.Carrier face.seedState :=
  rfl

@[simp] theorem generatedTable_component_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.generatedTable.component 0 =
      face.actualProcess.component face.seedState :=
  rfl

theorem generatedTableOccurrence_projects_to_root
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.generatedTableOccurrence.map Prod.fst = face.root := by
  unfold generatedTableOccurrence root
  rw [RootedAccountedUnfolding.map_map]
  rfl

theorem successorOccurrence_projects_to_root
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    successorOccurrence.map Prod.fst = face.root :=
  projects

/-! ## Frozen cofinal global-state consumption -/

abbrev StageCarrier
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) : Type u :=
  face.generatedTable.Carrier stage

abbrev CofinalGenerator := ULift.{u, 0} ℤ

/-- Fold-generated local evaluator for the one current component. -/
def localEvaluator
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) : CofinalGenerator →+ face.StageCarrier stage where
  toFun coefficient :=
    coefficient.down • face.generatedTable.component stage
  map_zero' := by simp
  map_add' left right := by
    simp [add_zsmul]

def localTransition
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.StageCarrier (stage + 1) →+ face.StageCarrier stage :=
  face.generatedTable.restriction stage

theorem localCompatibility
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    (face.localTransition stage).comp (face.localEvaluator (stage + 1)) =
      face.localEvaluator stage := by
  apply AddMonoidHom.ext
  intro coefficient
  rcases coefficient with ⟨coefficient⟩
  change face.generatedTable.restriction stage
      (coefficient • face.generatedTable.component (stage + 1)) =
    coefficient • face.generatedTable.component stage
  rw [map_zsmul, face.generatedTable.component_succ stage]

def cofinalEvaluatorData
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    AdditiveCofinalEvaluatorData CofinalGenerator face.StageCarrier where
  evaluator := face.localEvaluator
  transition := face.localTransition

def cofinalDependentOccurrence
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootedAccountedUnfolding
      (Root × AdditiveCofinalEvaluatorData CofinalGenerator
        face.StageCarrier) :=
  face.generatedTableOccurrence.map fun payload =>
    (payload.1, face.cofinalEvaluatorData)

def cofinalCompletionFace
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootGeneratedCofinalKernelCompletionAt
      face.cofinalDependentOccurrence :=
  RootGeneratedCofinalKernelCompletionAt.generate

@[simp] theorem cofinalCompletionFace_evaluator
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.cofinalCompletionFace.evaluator stage =
      face.localEvaluator stage := by
  unfold cofinalCompletionFace
    RootGeneratedCofinalKernelCompletionAt.evaluator
    RootGeneratedCofinalKernelCompletionAt.data
    RootGeneratedCofinalKernelCompletionAt.dataOccurrence
    cofinalDependentOccurrence cofinalEvaluatorData
  simp only [RootedAccountedUnfolding.root_map]

@[simp] theorem cofinalCompletionFace_transition
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.cofinalCompletionFace.transition stage =
      face.localTransition stage := by
  unfold cofinalCompletionFace
    RootGeneratedCofinalKernelCompletionAt.transition
    RootGeneratedCofinalKernelCompletionAt.data
    RootGeneratedCofinalKernelCompletionAt.dataOccurrence
    cofinalDependentOccurrence cofinalEvaluatorData
  simp only [RootedAccountedUnfolding.root_map]

theorem compatibilityCalculation
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootGeneratedCofinalKernelCompletionAt.GeneratedCompatibilityCalculationAt
      face.cofinalCompletionFace :=
  by
    apply face.cofinalCompletionFace.generateCompatibility
    intro stage
    rw [face.cofinalCompletionFace_transition,
      face.cofinalCompletionFace_evaluator,
      face.cofinalCompletionFace_evaluator]
    exact face.localCompatibility stage

/-- Framework-generated common component in the actual carrier limit. -/
noncomputable def globalComponent
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.cofinalCompletionFace.carrierLimit :=
  face.cofinalCompletionFace.completionRealization
    face.compatibilityCalculation
      (face.cofinalCompletionFace.completionMap
        face.compatibilityCalculation (ULift.up (1 : ℤ)))

/-- Every local row is now a restriction of one framework-generated global
component. -/
theorem globalComponent_restriction
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.cofinalCompletionFace.carrierRestriction stage
        face.globalComponent =
      face.generatedTable.component stage := by
  have generated := CategoryTheory.ConcreteCategory.congr_hom
    (face.cofinalCompletionFace.source_to_carrier_restriction
      face.compatibilityCalculation stage) (ULift.up (1 : ℤ))
  change face.cofinalCompletionFace.carrierRestriction stage
      face.globalComponent =
    face.cofinalCompletionFace.evaluator stage (ULift.up (1 : ℤ)) at generated
  rw [face.cofinalCompletionFace_evaluator] at generated
  simpa [localEvaluator] using generated

/-- The frozen residual-tower engine owns the global coverage settlement;
no positive branch is selected here. -/
def coverageResidualFace
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootGeneratedCofinalCoverageResidualTowerAt
      face.cofinalCompletionFace face.compatibilityCalculation :=
  RootGeneratedCofinalCoverageResidualTowerAt.generate

noncomputable def residualHistorySettlement
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :=
  face.coverageResidualFace.settleResidualHistory

theorem cofinalGlobalState_preserves_generated_root
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.cofinalCompletionFace.root = face.root ∧
      face.coverageResidualFace.root = face.root := by
  have completionRoot : face.cofinalCompletionFace.root = face.root := by
    unfold cofinalCompletionFace
      RootGeneratedCofinalKernelCompletionAt.root
      cofinalDependentOccurrence
    rw [RootedAccountedUnfolding.map_map]
    exact face.generatedTableOccurrence_projects_to_root
  exact ⟨completionRoot, by
    change face.cofinalCompletionFace.root = face.root
    exact completionRoot⟩

end RootGeneratedCofinalPrimePowerRestrictionHistoryAt

/-- Low-level consumer of the framework-generated table.  Its table
constructor is private, so this face cannot be activated directly by a
domain-supplied completed future. -/
structure RootGeneratedCofinalPrimePowerRestrictionRigidityAt
    {Root : Type w}
    (dependentOccurrence : RootedAccountedUnfolding
      (Root × CofinalPrimePowerRestrictionTableAt.{u}))
    (seedFiniteGenerated :
      AddGroup.FG (dependentOccurrence.root.2.Carrier 0)) : Type (max u w) where
  private mk ::

namespace RootGeneratedCofinalPrimePowerRestrictionRigidityAt

variable {Root : Type w}
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × CofinalPrimePowerRestrictionTableAt.{u})}
variable {seedFiniteGenerated :
  AddGroup.FG (dependentOccurrence.root.2.Carrier 0)}

def generate : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
    dependentOccurrence seedFiniteGenerated :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    RootedAccountedUnfolding Root :=
  dependentOccurrence.map Prod.fst

def actualTable
    (_face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    CofinalPrimePowerRestrictionTableAt :=
  dependentOccurrence.root.2

abbrev SeedCarrier
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) : Type u :=
  face.actualTable.Carrier 0

/-- Framework-owned iteration of domain successor arrows. -/
def restrictionToSeed
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    (stage : Nat) → face.actualTable.Carrier stage →+ face.SeedCarrier
  | 0 => AddMonoidHom.id _
  | stage + 1 =>
      (face.restrictionToSeed stage).comp
        (face.actualTable.restriction stage)

theorem restrictionToSeed_component
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    ∀ stage,
      face.restrictionToSeed stage (face.actualTable.component stage) =
        face.actualTable.component 0
  | 0 => rfl
  | stage + 1 => by
      change face.restrictionToSeed stage
          (face.actualTable.restriction stage
            (face.actualTable.component (stage + 1))) =
        face.actualTable.component 0
      rw [face.actualTable.component_succ stage,
        face.restrictionToSeed_component stage]

/-- Composite restriction from a later generated row to an arbitrary base
row, expressed by its offset. -/
def restrictionFromOffset
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    (offset : Nat) →
      face.actualTable.Carrier (base + offset) →+
        face.actualTable.Carrier base
  | 0 => AddMonoidHom.id _
  | offset + 1 =>
      (face.restrictionFromOffset base offset).comp
        (face.actualTable.restriction (base + offset))

theorem restrictionFromOffset_component
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    ∀ offset,
      face.restrictionFromOffset base offset
          (face.actualTable.component (base + offset)) =
        face.actualTable.component base
  | 0 => rfl
  | offset + 1 => by
      change face.restrictionFromOffset base offset
          (face.actualTable.restriction (base + offset)
            (face.actualTable.component (base + offset + 1))) =
        face.actualTable.component base
      rw [face.actualTable.component_succ (base + offset),
        face.restrictionFromOffset_component base offset]

def carrierCast
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    {source target : Nat} (equality : source = target) :
    face.actualTable.Carrier source →+
      face.actualTable.Carrier target := by
  subst target
  exact AddMonoidHom.id _

theorem carrierCast_component
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    {source target : Nat} (equality : source = target) :
    face.carrierCast equality (face.actualTable.component source) =
      face.actualTable.component target := by
  subst target
  rfl

def restrictionBetween
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base target : Nat) (order : base ≤ target) :
    face.actualTable.Carrier target →+
      face.actualTable.Carrier base :=
  (face.restrictionFromOffset base (target - base)).comp
    (face.carrierCast (Nat.add_sub_of_le order).symm)

theorem restrictionBetween_component
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base target : Nat) (order : base ≤ target) :
    face.restrictionBetween base target order
        (face.actualTable.component target) =
      face.actualTable.component base := by
  unfold restrictionBetween
  change face.restrictionFromOffset base (target - base)
      (face.carrierCast (Nat.add_sub_of_le order).symm
        (face.actualTable.component target)) =
    face.actualTable.component base
  rw [face.carrierCast_component,
    face.restrictionFromOffset_component]

/-- Generic quotient-zero elimination at one actual local row. -/
def localDivisionRootAt
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (stage : Nat) :
    { root : face.actualTable.Carrier stage //
      (scheduledPrime stage : Nat) ^ scheduledExponent stage • root =
        face.actualTable.component stage } :=
  PrimePowerQuotientEvaluation.divisionRootOfRangeMembership
    (face.actualTable.Carrier stage)
    (face.actualTable.component stage)
    (scheduledPrime stage) (scheduledExponent stage)
    (PrimePowerQuotientEvaluation.rangeMembershipOfQuotientZero
      (face.actualTable.Carrier stage)
      (face.actualTable.component stage)
      (scheduledPrime stage) (scheduledExponent stage)
      (face.actualTable.quotientZero stage))

/-- Cofinal repetition places every requested prime power after any chosen
base row; the framework transports that local root back along generated
successors. -/
def requestedDivisionRootAt
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) (prime : Nat.Primes) (exponent : Nat) :
    face.actualTable.Carrier base :=
  let target := scheduleIndexAfter prime exponent base
  face.restrictionBetween base target
      (lower_le_scheduleIndexAfter prime exponent base)
    (face.localDivisionRootAt target)

theorem requestedDivisionRootAt_landing
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) (prime : Nat.Primes) (exponent : Nat)
    (positive : 0 < exponent) :
    (prime : Nat) ^ exponent •
        face.requestedDivisionRootAt base prime exponent =
      face.actualTable.component base := by
  unfold requestedDivisionRootAt
  let target := scheduleIndexAfter prime exponent base
  let order : base ≤ target :=
    lower_le_scheduleIndexAfter prime exponent base
  have localLanding := (face.localDivisionRootAt target).property
  have mapped := congrArg
    (face.restrictionBetween base target order) localLanding
  rw [map_nsmul, face.restrictionBetween_component] at mapped
  simpa only [target, scheduledPrime_scheduleIndexAfter,
    scheduledExponent_scheduleIndexAfter prime exponent base positive]
    using mapped

def quotientFaceAt
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    RootGeneratedPrimePowerQuotientEvaluationAt
      (face.actualTable.Carrier base) face.root
        (face.actualTable.finiteGenerated base) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate
    (face.actualTable.Carrier base)

def quotientEvaluatorAt
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    face.actualTable.Carrier base →
      PrimePowerQuotientEvaluation.State
        (face.actualTable.Carrier base) :=
  (face.quotientFaceAt base).accountedEvaluator

theorem componentAt_quotientZero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) (prime : Nat.Primes) (exponent : Nat) :
    face.quotientEvaluatorAt base (face.actualTable.component base)
        prime exponent = 0 := by
  unfold quotientEvaluatorAt
  rw [(face.quotientFaceAt base).accountedEvaluator_eq_canonical]
  apply (QuotientAddGroup.eq_zero_iff
    (face.actualTable.component base)).2
  cases exponent with
  | zero => exact ⟨face.actualTable.component base, by simp⟩
  | succ exponent =>
      exact ⟨face.requestedDivisionRootAt base prime (exponent + 1),
        face.requestedDivisionRootAt_landing base prime (exponent + 1)
          (by omega)⟩

theorem componentAt_evaluatorZero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    face.quotientEvaluatorAt base (face.actualTable.component base) = 0 := by
  funext prime exponent
  exact face.componentAt_quotientZero base prime exponent

def rigidityFaceAt
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      (face.quotientFaceAt base).dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem componentAt_eq_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (base : Nat) :
    face.actualTable.component base = 0 := by
  apply (face.rigidityFaceAt base).evaluator_eq_zero_implies_element_zero
    (face.actualTable.component base)
  rw [(face.rigidityFaceAt base).actualMaterial_eq]
  simp only [RootGeneratedPrimePowerQuotientEvaluationAt.dependentOccurrence,
    RootedAccountedUnfolding.root_map]
  change face.quotientEvaluatorAt base
    (face.actualTable.component base) = 0
  exact face.componentAt_evaluatorZero base

/-- The local root is transported by the generated composite restriction,
not supplied at the seed. -/
def seedDivisionRootAtCursor
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (stage : Nat) : face.SeedCarrier :=
  face.restrictionToSeed stage (face.localDivisionRootAt stage)

theorem seedDivisionRootAtCursor_landing
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (stage : Nat) :
    (scheduledPrime stage : Nat) ^ scheduledExponent stage •
        face.seedDivisionRootAtCursor stage =
      face.actualTable.component 0 := by
  unfold seedDivisionRootAtCursor
  rw [← map_nsmul, (face.localDivisionRootAt stage).property,
    face.restrictionToSeed_component stage]

def requestedSeedDivisionRoot
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (prime : Nat.Primes) (exponent : Nat) : face.SeedCarrier :=
  face.seedDivisionRootAtCursor (scheduleIndex prime exponent)

theorem requestedSeedDivisionRoot_landing
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (prime : Nat) ^ exponent •
        face.requestedSeedDivisionRoot prime exponent =
      face.actualTable.component 0 := by
  unfold requestedSeedDivisionRoot
  have landing := face.seedDivisionRootAtCursor_landing
    (scheduleIndex prime exponent)
  simpa only [scheduledPrime_scheduleIndex,
    scheduledExponent_scheduleIndex prime exponent positive] using landing

def quotientFace
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    RootGeneratedPrimePowerQuotientEvaluationAt face.SeedCarrier
      face.root seedFiniteGenerated :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate face.SeedCarrier

def quotientEvaluator
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    face.SeedCarrier → PrimePowerQuotientEvaluation.State face.SeedCarrier :=
  face.quotientFace.accountedEvaluator

theorem seedComponent_quotientZero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated)
    (prime : Nat.Primes) (exponent : Nat) :
    face.quotientEvaluator (face.actualTable.component 0)
        prime exponent = 0 := by
  unfold quotientEvaluator
  rw [face.quotientFace.accountedEvaluator_eq_canonical]
  apply (QuotientAddGroup.eq_zero_iff
    (face.actualTable.component 0)).2
  cases exponent with
  | zero => exact ⟨face.actualTable.component 0, by simp⟩
  | succ exponent =>
      exact ⟨face.requestedSeedDivisionRoot prime (exponent + 1),
        face.requestedSeedDivisionRoot_landing
          prime (exponent + 1) (by omega)⟩

theorem seedComponent_evaluatorZero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    face.quotientEvaluator (face.actualTable.component 0) = 0 := by
  funext prime exponent
  exact face.seedComponent_quotientZero prime exponent

def rigidityFace
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      face.quotientFace.dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem seedComponent_eq_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    face.actualTable.component 0 = 0 := by
  apply face.rigidityFace.evaluator_eq_zero_implies_element_zero
    (face.actualTable.component 0)
  rw [face.rigidityFace.actualMaterial_eq]
  simp only [RootGeneratedPrimePowerQuotientEvaluationAt.dependentOccurrence,
    RootedAccountedUnfolding.root_map]
  change face.quotientEvaluator (face.actualTable.component 0) = 0
  exact face.seedComponent_evaluatorZero

theorem seedQuotientEvaluatorSourceKernelResidualZero
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt.GeneratedSourceKernelResidualZeroAt
      face.rigidityFace.faithfulFace face.rigidityFace.additiveCalculation :=
  face.rigidityFace.sourceKernelResidualZero

noncomputable def seedQuotientEvaluatorSourceComponentEquiv
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :=
  face.rigidityFace.canonicalSourceComponentEquiv

theorem preserves_exact_root_and_local_table
    (face : RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      dependentOccurrence seedFiniteGenerated) :
    face.root = dependentOccurrence.map Prod.fst ∧
      face.actualTable = dependentOccurrence.root.2 ∧
      face.quotientFace.dependentOccurrence.map Prod.fst = face.root :=
  ⟨rfl, rfl, face.quotientFace.dependentOccurrence_projects_to_root⟩

end RootGeneratedCofinalPrimePowerRestrictionRigidityAt

namespace RootGeneratedCofinalPrimePowerRestrictionHistoryAt

variable {Root : Type w} {State : Type u}
variable {seedOccurrence : RootedAccountedUnfolding (Root × State)}
variable {successorOccurrence : RootedAccountedUnfolding
  (Root × PrimePowerRestrictionLocalProcessAt State)}
variable {projects : successorOccurrence.map Prod.fst =
  seedOccurrence.map Prod.fst}
variable {seedCursor : successorOccurrence.root.2.cursor
  seedOccurrence.root.2 = 0}

/-- The seed FG receipt is transported only across the definitionally
generated stage-zero readout. -/
theorem generatedSeedFiniteGenerated
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    AddGroup.FG (face.generatedTableOccurrence.root.2.Carrier 0) := by
  rw [face.generatedTableOccurrence_root_table,
    face.generatedTable_carrier_zero]
  exact face.actualProcess.finiteGenerated face.seedState

/-- Direct splice from generated history into the low-level arithmetic
consumer.  The only FG fact is the one generated for the seed carrier. -/
def rigidityConsumer
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    RootGeneratedCofinalPrimePowerRestrictionRigidityAt
      face.generatedTableOccurrence
        face.generatedSeedFiniteGenerated :=
  RootGeneratedCofinalPrimePowerRestrictionRigidityAt.generate

theorem generatedSeedComponent_eq_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.actualProcess.component face.seedState = 0 := by
  have generated :=
    face.rigidityConsumer.seedComponent_eq_zero
  change face.generatedTableOccurrence.root.2.component 0 = 0 at generated
  rw [face.generatedTableOccurrence_root_table,
    face.generatedTable_component_zero] at generated
  exact generated

theorem generatedComponentAt_eq_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor)
    (stage : Nat) :
    face.generatedTable.component stage = 0 := by
  have generated := face.rigidityConsumer.componentAt_eq_zero stage
  change face.generatedTableOccurrence.root.2.component stage = 0 at generated
  rw [face.generatedTableOccurrence_root_table] at generated
  exact generated

theorem generatedSeedSourceKernelResidualZero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt.GeneratedSourceKernelResidualZeroAt
      face.rigidityConsumer.rigidityFace.faithfulFace
      face.rigidityConsumer.rigidityFace.additiveCalculation :=
  face.rigidityConsumer.seedQuotientEvaluatorSourceKernelResidualZero

noncomputable def generatedSeedSourceComponentEquiv
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :=
  face.rigidityConsumer.seedQuotientEvaluatorSourceComponentEquiv

theorem generated_history_table_rigidity_preserves_root
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    successorOccurrence.map Prod.fst = face.root ∧
      face.generatedTableOccurrence.map Prod.fst = face.root ∧
      (face.rigidityConsumer.quotientFace
        ).dependentOccurrence.map Prod.fst = face.root := by
  exact ⟨face.successorOccurrence_projects_to_root,
    face.generatedTableOccurrence_projects_to_root,
    face.rigidityConsumer.quotientFace
      |>.dependentOccurrence_projects_to_root |>.trans
        face.generatedTableOccurrence_projects_to_root⟩

private def globalElementHom
    {G : Type u} [AddCommGroup G] (element : G) :
    CofinalGenerator →+ G where
  toFun coefficient := coefficient.down • element
  map_zero' := by simp
  map_add' left right := by simp [add_zsmul]

/-- Cofinal repetition gives every local restriction its own all-prime
rigidity proof.  Joint monicity of the limit restrictions then kills the
framework-generated global component itself. -/
theorem generatedGlobalComponent_eq_zero
    (face : RootGeneratedCofinalPrimePowerRestrictionHistoryAt
      seedOccurrence successorOccurrence projects seedCursor) :
    face.globalComponent = 0 := by
  have homEquality :
      (AddCommGrpCat.ofHom (globalElementHom face.globalComponent) :
          AddCommGrpCat.of CofinalGenerator ⟶
            face.cofinalCompletionFace.carrierLimit) = 0 := by
    apply (limit.isLimit face.cofinalCompletionFace.carrierTower).hom_ext
    intro index
    rcases index with ⟨stage⟩
    simp only [Limits.zero_comp]
    change AddCommGrpCat.ofHom (globalElementHom face.globalComponent) ≫
        face.cofinalCompletionFace.carrierRestriction stage = 0
    apply AddCommGrpCat.ext
    intro coefficient
    rcases coefficient with ⟨coefficient⟩
    change face.cofinalCompletionFace.carrierRestriction stage
          (coefficient • face.globalComponent) = 0
    rw [map_zsmul, face.globalComponent_restriction,
      face.generatedComponentAt_eq_zero stage, smul_zero]
  have atOne := CategoryTheory.ConcreteCategory.congr_hom
    homEquality (ULift.up (1 : ℤ))
  change (1 : ℤ) • face.globalComponent = 0 at atOne
  simpa only [one_zsmul] using atOne

end RootGeneratedCofinalPrimePowerRestrictionHistoryAt

end
end CofinalPrimePowerRestrictionRigidity
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
