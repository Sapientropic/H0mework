import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Receipt
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Noetherian

/-! The actual post-birth inquiry current supplies its canonical payment,
original physical occurrence and pinned paid history to existing consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Consumer

open SourceOperationEffects SourceOperationExecution SourceOperationNative
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
open DebtActivationWorld DebtActivationLedger RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace Unit
export RootGeneratedDebtActivationJointSource.Unit
  (native finiteVisit sourceRow rowInventory patch targetRow targetRow_inventory supportAt JointV)
end Unit

noncomputable section
variable (runtime : LivingRuntimeState process)

theorem actual_node (depth : Nat) :
    ((inquiryRuntime runtime).stateAt (depth + 1)).engine.node =
      .active (mathPresentation runtime depth) := stateAt_afterBirth_node runtime depth

private theorem finiteBudget (count : Nat) :
    remaining (Unit.finiteVisit (registered runtime) count).current.2.state.1 = 10 - count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have stateEq := (Unit.native (registered runtime) (Unit.finiteVisit (registered runtime) count).current).next_state
      change remaining (Unit.native (registered runtime)
        (Unit.finiteVisit (registered runtime) count).current).nextEvent.state.1 = 10 - (count + 1)
      have debit := RootGeneratedDebtActivationJointSource.Unit.mathTarget_budget
        (Unit.finiteVisit (registered runtime) count).current.2
      exact (congrArg (fun state => remaining state.1) stateEq).trans
        (debit.trans (by rw [ih, Nat.sub_sub]))

private theorem finiteOriginal (count : Nat) :
    (Unit.finiteVisit (registered runtime) count).current.1 =
      SourcePhysicalCalculation.baseCurrent (runtime.advance count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change CanonicalUnitArithmeticRoot.next
        (Unit.finiteVisit (registered runtime) count).current.1 =
        SourcePhysicalCalculation.baseCurrent (runtime.advance count).tick.next
      exact (congrArg CanonicalUnitArithmeticRoot.next ih).trans
        (SourcePhysicalCalculation.original_next (runtime.advance count))

theorem current_original (depth : Nat) : (mathCurrent runtime depth).1 =
    SourcePhysicalCalculation.baseCurrent (runtime.advance (depth + 1)) := finiteOriginal runtime (depth + 1)

def budget (depth : Nat) : Nat := remaining (mathCurrent runtime depth).2.state.1

theorem budget_eq (depth : Nat) : budget runtime depth = 10 - (depth + 1) := finiteBudget runtime (depth + 1)

def occurrence (depth : Nat) := (targetRoot runtime).emitted (mathCurrent runtime depth)

def history (depth : Nat) : (SourcePhysicalCalculation.calculationLaw runtime).DebtState :=
  (mathCurrent runtime depth).2.state

def receipt (depth : Nat) :
    RelationIndex ℤ (SourcePhysicalCalculation.rawEnvironment runtime) (Sum.inl OperationSort.parent) →₀ ℤ :=
  (history runtime depth).2.relationWords

def boundary (depth : Nat) :
    Formal ℤ SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar
      (Sum.inl OperationSort.parent) :=
  relationMap (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime) (receipt runtime depth)

theorem trace_accounting (depth : Nat) : (history runtime depth).2.length + budget runtime depth = 10 :=
  (history runtime depth).2.remaining_eq.symm

theorem pinned_pair (depth : Nat) : (history runtime depth).1.eval (SourcePhysicalCalculation.rawEnvironment runtime) =
    ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (history runtime depth).2.sound.symm.trans (SourcePhysicalCalculation.raw_value runtime)

def originalOccurrence (depth : Nat) : CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt
    (mathCurrent runtime depth).1 := Joint.originalOccurrence (registered runtime) (occurrence runtime depth)

def physicalActive (depth : Nat) : projectionLaw.ActiveAt PUnit.unit (originalOccurrence runtime depth) :=
  ⟨by
    rw [current_original]
    exact (activeAt (runtime.advance (depth + 1))).down⟩

def physicalPayload (depth : Nat) := projectionLaw.project PUnit.unit
  (originalOccurrence runtime depth) (physicalActive runtime depth)

def physicalPair (depth : Nat) : ParentCarrier × ParentCarrier :=
  ((physicalPayload runtime depth).sourceState, (physicalPayload runtime depth).forcedTrace)

theorem physicalPair_eq (depth : Nat) : physicalPair runtime depth =
    ((payloadAt (runtime.advance (depth + 1))).sourceState,
      (payloadAt (runtime.advance (depth + 1))).forcedTrace) := by
  apply Prod.ext
  · exact (physicalPayload runtime depth).sourceState_eq.trans
      ((congrArg sourceStateAt (current_original runtime depth)).trans
        (payloadAt (runtime.advance (depth + 1))).sourceState_eq.symm)
  · exact (physicalPayload runtime depth).forcedTrace_eq.trans
      ((congrArg (fun current => (operationValuesAt current).sum) (current_original runtime depth)).trans
        (payloadAt (runtime.advance (depth + 1))).forcedTrace_eq.symm)

def physicalEnvironment (depth : Nat) : Env SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar :=
  SourcePhysicalCalculation.rawEnvironment (runtime.advance (depth + 1))

def physicalProjection : (targetRoot runtime).source.base.projectionLaw.Projection :=
  (targetOldInstallation runtime).embed (.component PUnit.unit)

theorem physical_outcome (depth : Nat) :
    HEq ((targetRoot runtime).source.base.projectionLaw.outcomeAt
      (physicalProjection runtime) (occurrence runtime depth))
      (.inl ⟨physicalActive runtime depth, physicalPayload runtime depth⟩ :
        SourceNativeProjectionFiberAt projectionLaw PUnit.unit (originalOccurrence runtime depth)) := by
  have source := ((targetOldInstallation runtime).outcome_heq (occurrence runtime depth) (.component PUnit.unit)).trans
    (((physicalInstallation runtime).outcome_heq (occurrence runtime depth) PUnit.unit).trans
      (SourcePhysicalCalculationAdmission.physical_outcome runtime (occurrence runtime depth) PUnit.unit))
  have seen : projectionLaw.outcomeAt PUnit.unit (originalOccurrence runtime depth) =
      .inl ⟨physicalActive runtime depth, physicalPayload runtime depth⟩ := by
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classifier : projectionLaw.classify PUnit.unit (originalOccurrence runtime depth) = result
    cases result with
    | inl active =>
        have same : active = physicalActive runtime depth := PLift.down_injective (Subsingleton.elim _ _)
        cases same
        rfl
    | inr inactive =>
        have positive := (physicalActive runtime depth).down
        have zero := inactive.down
        omega
  exact source.trans (heq_of_eq seen)

theorem physical_inverse (depth : Nat) (alternative : ParentCarrier) :
    jointMeasurement alternative = jointMeasurement (physicalPayload runtime depth).targetState ↔
      alternative - (physicalPayload runtime depth).targetState ∈ JointMeasurementKernel :=
  (physicalPayload runtime depth).inverseFibreLaw alternative

theorem physical_pair_inverse (depth : Nat) (alternative : ParentCarrier) :
    jointMeasurement alternative = jointMeasurement (physicalPayload runtime depth).targetState ↔
      alternative - ((physicalPair runtime depth).1 + (physicalPair runtime depth).2) ∈ JointMeasurementKernel := by
  change _ ↔ alternative - ((physicalPayload runtime depth).sourceState +
    (physicalPayload runtime depth).forcedTrace) ∈ _
  rw [← (physicalPayload runtime depth).stateUpdate]
  exact physical_inverse runtime depth alternative

theorem current_pair_read (depth : Nat) :
    SourcePhysicalCalculation.rawExpression.eval (physicalEnvironment runtime depth) = physicalPair runtime depth :=
  (SourcePhysicalCalculation.raw_value (runtime.advance (depth + 1))).trans (physicalPair_eq runtime depth).symm

theorem residual_read (depth : Nat) :
    (residualEquivRange (evaluation (R := ℤ) (physicalEnvironment runtime depth))
      (canonicalResidual (evaluation (R := ℤ) (physicalEnvironment runtime depth))
        (boundary runtime depth))).val =
      physicalPair runtime depth - (history runtime depth).1.eval (physicalEnvironment runtime depth) := by
  change evaluation (R := ℤ) (s := Sum.inl OperationSort.parent)
    (physicalEnvironment runtime depth) (boundary runtime depth) = _
  rw [show boundary runtime depth = _ from (history runtime depth).2.relation_boundary, map_sub]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul]
  exact congrArg (fun value => value - (history runtime depth).1.eval (physicalEnvironment runtime depth))
    (current_pair_read runtime depth)

theorem residual_zero_iff (depth : Nat) :
    canonicalResidual (evaluation (R := ℤ) (physicalEnvironment runtime depth)) (boundary runtime depth) = 0 ↔
      physicalPair runtime depth = (history runtime depth).1.eval (physicalEnvironment runtime depth) := by
  rw [canonicalResidual_eq_zero_iff]
  change (residualEquivRange (evaluation (R := ℤ) (physicalEnvironment runtime depth))
    (canonicalResidual (evaluation (R := ℤ) (physicalEnvironment runtime depth))
      (boundary runtime depth))).val = 0 ↔ _
  rw [residual_read, sub_eq_zero]

theorem residual_inventory (depth : Nat) :
    updateInventory (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime)
        (physicalEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime)
        (boundary runtime depth) =
      (0, physicalPair runtime depth - (history runtime depth).1.eval (physicalEnvironment runtime depth)) := by
  have envEq : SourcePhysicalCalculation.rawEnvironment runtime +
      (physicalEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime) =
        physicalEnvironment runtime depth := by abel
  have effect := (history runtime depth).2.updated_residual (R := ℤ)
    (physicalEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime)
  rw [envEq] at effect
  exact ((history runtime depth).2.relation_inventory
    (physicalEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime)).trans
      (congrArg (fun value => (0, value)) (effect.symm.trans (residual_read runtime depth)))

theorem zero_budget_residual (depth : Nat) (zero : budget runtime depth = 0) :
    (residualEquivRange (evaluation (R := ℤ) (physicalEnvironment runtime depth))
      (canonicalResidual (evaluation (R := ℤ) (physicalEnvironment runtime depth))
        (boundary runtime depth))).val =
      physicalPair runtime depth - ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) := by
  let settled := RootGeneratedDebtActivationJointSource.Unit.localSettlement (mathCurrent runtime depth).2 zero
  have read : (history runtime depth).1.eval (physicalEnvironment runtime depth) =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
    (congrArg (fun expression => expression.eval (physicalEnvironment runtime depth)) settled.2.down).trans
      ((SourceOperationExecutionDebt.completed_value (history runtime depth) settled).trans
        (SourcePhysicalCalculation.raw_value runtime))
  exact (residual_read runtime depth).trans (congrArg (fun value => physicalPair runtime depth - value) read)

private def causalDepth (current : SourceNativeLivingRootCurrentAt (NewN runtime)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem finiteDepth (count : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth (Unit.finiteVisit (registered runtime) count).history = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (Unit.finiteVisit (registered runtime) count).history + 1 = count + 1
      rw [ih]

/-- Fixed-network restriction of the actual inquiry nodes after birth;
`postBirthProcess_actual` and `macro_next_actual` retain their complete source. -/
def postBirthProcess : SourceNativeLivingRootProcess (NewN runtime) where
  State := Nat
  stateAt := fun depth => ⟨Joint.JointV (registered runtime), targetRoot runtime, mathVisit runtime depth⟩
  stateAt_injective := by
    intro left right same
    have depths := congrArg (causalDepth runtime) same
    change some (ProductiveFiniteRootHistoryAt.causalDepth
      (Unit.finiteVisit (registered runtime) (left + 1)).history) =
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (Unit.finiteVisit (registered runtime) (right + 1)).history) at depths
    rw [finiteDepth, finiteDepth] at depths
    exact Nat.add_right_cancel (Option.some.inj depths)
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

def debtCurrent (depth : Nat) : SourceNativeRootDebtCurrentAt
    (postBirthProcess runtime) (mathEntry runtime 0) where
  state := depth
  entry := mathEntry runtime depth
  sameDebt := ⟨rfl, rfl⟩

theorem postBirthProcess_actual (depth : Nat) :
    ((inquiryRuntime runtime).stateAt (depth + 1)).engine.node.erase =
      (⟨NewN runtime,
        ⟨Joint.JointV (registered runtime), (targetRoot runtime).toAuthoritativeRoot, mathVisit runtime depth⟩⟩ :
        AnyAuthoritativeRootCurrent) := by
  rw [actual_node]
  rfl

theorem macro_next_actual (depth : Nat) :
    ((inquiryRuntime runtime).tickAt (depth + 1)).next.node.erase =
      (⟨NewN runtime,
        ⟨Joint.JointV (registered runtime), (targetRoot runtime).toAuthoritativeRoot,
          mathVisit runtime (depth + 1)⟩⟩ : AnyAuthoritativeRootCurrent) :=
  (congrArg (fun engine => engine.node.erase)
    (SourceNativeInquiryRuntime.stateAt_succ_engine (inquiryRuntime runtime) (depth + 1))).symm.trans
      (postBirthProcess_actual runtime (depth + 1))

def canonicalSuccessor (depth : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      ((targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (mathVisit runtime depth)).occurrence
      ((targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (mathVisit runtime depth)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit runtime depth)).wholeLedgerWriteBack).get (by rfl)

theorem canonical_next (depth : Nat) : (canonicalSuccessor runtime depth).targetCurrent =
    mathCurrent runtime (depth + 1) := rfl

private theorem destination_math (depth : Nat) :
    ((canonicalSuccessor runtime depth).ledgerEvolution.destination
      (mathEntry runtime depth)).1 = mathEntry runtime (depth + 1) := by
  change Unit.targetRow (registered runtime) (mathCurrent runtime depth)
    ((Unit.rowInventory (registered runtime) (mathCurrent runtime depth)).backward
      ((Unit.rowInventory (registered runtime) (mathCurrent runtime depth)).forward 1)) = _
  rw [(Unit.rowInventory (registered runtime) (mathCurrent runtime depth)).backward_forward]
  exact Unit.targetRow_inventory (registered runtime) (mathCurrent runtime depth) 1

def debtStep (depth : Nat) : SourceNativeRootDebtStepAt (debtCurrent runtime depth) where
  targetEntry := ((canonicalSuccessor runtime depth).ledgerEvolution.destination
    (mathEntry runtime depth)).1
  evolution := ((canonicalSuccessor runtime depth).ledgerEvolution.destination
    (mathEntry runtime depth)).2
  sameDebtTarget_unique := by
    intro entry same
    have unique : entry = mathEntry runtime (depth + 1) := by
      rcases entry with ⟨responsibility, opened⟩
      cases responsibility with
      | inl old => exact nomatch same.claim_eq
      | inr debt => cases debt; rcases opened with ⟨⟨proof⟩⟩; rfl
    exact unique.trans (destination_math runtime depth).symm

def payment (depth : Nat) (positive : 0 < budget runtime depth) :
    SourceNativeRootDebtPaymentStepAt (debtCurrent runtime depth) where
  step := debtStep runtime depth
  strictDebit := by
    change ((debtStep runtime depth).targetEntry).progressBudget < (mathEntry runtime depth).progressBudget
    rw [show (debtStep runtime depth).targetEntry = mathEntry runtime (depth + 1) from destination_math runtime depth]
    change budget runtime (depth + 1) < budget runtime depth
    simp only [budget_eq] at positive ⊢
    omega

theorem paidContinuation_wellFounded :
    WellFounded (SourceNativePaidRootDebtContinuationRel
      (process := postBirthProcess runtime) (origin := mathEntry runtime 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

def paidContinuation (depth : Nat) (positive : 0 < budget runtime depth) :
    SourceNativePaidRootDebtMacroContinuationAt (debtCurrent runtime depth) :=
  .ofPayment .refl (payment runtime depth positive) .refl

end
end SourcePhysicalCalculationAdmission.Inquiry.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
