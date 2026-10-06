import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Consumer

/-! The existing source normal contributes its complete stage writes.
Only low source material is installed; the same high runtime history stays
in the producer body and supplies the actual-stage commuting square. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base baseRoot datum)
end S
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree
  (Raw Current World vocabulary law raw support supportAt initial action nextState whole mathEntry
   authoritativeRoot runtimeCurrent)
namespace Calculation
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (frontier normal seed)
end Calculation
namespace Completion
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (state runtime)
end Completion
end O
namespace CofaceTransport
open RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin → RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (component : SourceNativeProjectionLaw old.source.restructuringSource.toLedgerSource)
def extended : SourceNativeAuthoritativeRootClosure N V where
  source := old.source.withProjectionCoface component
  emitted := old.emitted
  compiler_commutes := old.compiler_commutes
theorem raw_same : RootGeneratedDebtActivationJointSource.OwnerFree.raw (extended old component) origin reader = RootGeneratedDebtActivationJointSource.OwnerFree.raw old origin reader := by
  unfold RootGeneratedDebtActivationJointSource.OwnerFree.raw extended
  change reader (old.emitted origin) = reader (old.emitted origin)
  rfl

private def rawNext (input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (state : SourceOperationExecutionDebt.State input.environment input.expression) :=
  match SourceOperationExecutionDebt.generate input.environment input.expression state with
  | .inl _ => state | .inr paid => paid.1
private theorem rawNext_heq {first second : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort)}
    (same : first = second)
    (left : SourceOperationExecutionDebt.State first.environment first.expression)
    (right : SourceOperationExecutionDebt.State second.environment second.expression) (stateEq : HEq left right) :
    HEq (rawNext first left) (rawNext second right) := by
  cases same
  cases stateEq
  rfl

private theorem next_raw (root : SourceNativeAuthoritativeRootClosure N V) (current : V.Current)
    (source : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (state : RootGeneratedDebtActivationJointSource.OwnerFree.Current root current source) :
    RootGeneratedDebtActivationJointSource.OwnerFree.nextState root current source state = rawNext (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source) state := by
  unfold RootGeneratedDebtActivationJointSource.OwnerFree.nextState RootGeneratedDebtActivationJointSource.OwnerFree.targetOf RootGeneratedDebtActivationJointSource.OwnerFree.action rawNext
  cases SourceOperationExecutionDebt.generate (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source).environment (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source).expression state <;> rfl

theorem next_same (state : RootGeneratedDebtActivationJointSource.OwnerFree.Current old origin reader) :
    RootGeneratedDebtActivationJointSource.OwnerFree.nextState (extended old component) origin reader state = RootGeneratedDebtActivationJointSource.OwnerFree.nextState old origin reader state :=
  (next_raw (extended old component) origin reader state).trans ((eq_of_heq (rawNext_heq (raw_same old origin reader component) state state HEq.rfl)).trans
    (next_raw old origin reader state).symm)
theorem state_preserved (count : Nat) : Completion.state (extended old component) origin reader count = Completion.state old origin reader count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      exact (Completion.next_state (extended old component) origin reader count).trans
        ((next_same old origin reader component _).trans
          ((congrArg (RootGeneratedDebtActivationJointSource.OwnerFree.nextState old origin reader) prior).trans
            (Completion.next_state old origin reader count).symm))

private def rawTarget (input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (state : SourceOperationExecutionDebt.State input.environment input.expression)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕ GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law input.environment input.expression) state) :=
  match selected with | .inl _ => state | .inr paid => paid.1

private def rawWholeOf (input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (support : N.Support) (state : SourceOperationExecutionDebt.State input.environment input.expression)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕ GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law input.environment input.expression) state) :
    LedgerWriteEvolutionAt (ExtendedNetwork N (RootGeneratedDebtActivationJointSource.Idle.law input.environment input.expression))
      (activeLedger support state) (activeLedger support (rawTarget input state selected)) :=
  match selected with
  | .inl settled => transportLedgerEvolution support (RootGeneratedDebtActivationJointSource.Idle.identityTransport state settled)
  | .inr paid => stepLedgerEvolution support paid.2

private def rawWhole (input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (support : N.Support) (state : SourceOperationExecutionDebt.State input.environment input.expression) :=
  rawWholeOf input support state (SourceOperationExecutionDebt.generate input.environment input.expression state)

private theorem rawWhole_heq
    {first second : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort)}
    (same : first = second) (support : N.Support)
    (left : SourceOperationExecutionDebt.State first.environment first.expression)
    (right : SourceOperationExecutionDebt.State second.environment second.expression) (stateEq : HEq left right) :
    HEq (rawWhole first support left) (rawWhole second support right) := by
  cases same
  cases stateEq
  rfl

private theorem whole_raw (root : SourceNativeAuthoritativeRootClosure N V) (current : V.Current)
    (source : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (state : RootGeneratedDebtActivationJointSource.OwnerFree.Current root current source) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole root current source state)
      (rawWhole (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source)
        (RootGeneratedDebtActivationJointSource.OwnerFree.support root current) state) := by
  unfold RootGeneratedDebtActivationJointSource.OwnerFree.whole RootGeneratedDebtActivationJointSource.OwnerFree.wholeOf
    RootGeneratedDebtActivationJointSource.OwnerFree.action rawWhole rawWholeOf rawTarget
  cases SourceOperationExecutionDebt.generate
    (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source).environment
    (RootGeneratedDebtActivationJointSource.OwnerFree.raw root current source).expression state <;> rfl

theorem whole_preserved
    (left : RootGeneratedDebtActivationJointSource.OwnerFree.Current (extended old component) origin reader)
    (right : RootGeneratedDebtActivationJointSource.OwnerFree.Current old origin reader) (same : HEq left right) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole (extended old component) origin reader left)
      (RootGeneratedDebtActivationJointSource.OwnerFree.whole old origin reader right) := by
  have support : RootGeneratedDebtActivationJointSource.OwnerFree.support (extended old component) origin =
      RootGeneratedDebtActivationJointSource.OwnerFree.support old origin := rfl
  have paired := rawWhole_heq (raw_same old origin reader component)
    (RootGeneratedDebtActivationJointSource.OwnerFree.support old origin) left right same
  exact (whole_raw (extended old component) origin reader left).trans
    (paired.trans (whole_raw old origin reader right).symm)

end CofaceTransport

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))

abbrev originRoot := (S.base frame).root.toAuthoritativeRoot
abbrev reader := fun (_ : (originRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) =>
  (S.datum frame programme).reader occurrence
abbrev calculationRoot := O.authoritativeRoot (originRoot frame) current (reader frame occurrence)
abbrev state (count : Nat) := O.Completion.state (originRoot frame) current (reader frame occurrence) count

abbrev StageMaterial (count : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.SourceMaterialAt (calculationRoot frame occurrence)
    ((calculationRoot frame occurrence).emitted (state frame occurrence count))

structure ReceiptAt : Type u where
  private mk ::
  raw : O.Raw (Value:=SourceOperationScalarInventoryLift.PairValue PhysicalValue)
    (Var:=Orbit.Var PhysicalVar) (sort:=sort)
  material : (count : Fin (remaining raw.expression + 1)) → StageMaterial frame occurrence count.1
  action : (count : Fin (remaining raw.expression + 1)) →
    SourceOperationExecutionDebt.Settlement (state frame occurrence count.1) ⊕
      GeneratedStepAt (O.law (originRoot frame) current (reader frame occurrence)) (state frame occurrence count.1)
  whole : (count : Fin (remaining raw.expression + 1)) → LedgerWriteEvolutionAt
    (O.World (originRoot frame) current (reader frame occurrence))
    ⟨O.supportAt (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)⟩
    ⟨O.supportAt (originRoot frame) current (reader frame occurrence)
      (O.nextState (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1))⟩

def receiptAt : ReceiptAt frame occurrence :=
  let raw := (S.datum frame programme).reader occurrence
  ⟨raw,
    fun count => RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      (calculationRoot frame occurrence)
      ((calculationRoot frame occurrence).emitted (state frame occurrence count.1)),
    fun count => O.action (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1),
    fun count => O.whole (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)⟩

def component : SourceNativeProjectionLaw (S.baseRoot frame programme).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => ReceiptAt frame occurrence
  project := fun _ {_current} occurrence _ => receiptAt frame occurrence

def stage (count : Fin ((O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).stageCount + 1)) :=
  (O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).history.stageAt count

theorem stage_factorizes (count : Fin ((O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).stageCount + 1)) :
    type_of% ((stage frame occurrence count).factorizes) := (stage frame occurrence count).factorizes

theorem material_stage (count : Fin ((O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).stageCount + 1)) :
    HEq ((receiptAt frame occurrence).material count).1.1
      (stage frame occurrence count).activated.generated.wholeLedgerWriteBack := HEq.rfl

theorem whole_stage (count : Fin ((O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).stageCount + 1)) :
    HEq (stage frame occurrence count).wholeLedgerWriteBack
      ((receiptAt frame occurrence).material count).1.1 := HEq.rfl

theorem stage_depth (count : Fin ((O.Calculation.frontier (originRoot frame) current (reader frame occurrence)).stageCount + 1)) :
    ((O.Calculation.seed (originRoot frame) current (reader frame occurrence)).advance count.1).state.down = count.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime_depth (originRoot frame) current
    (reader frame occurrence) count.1

theorem paid_whole (count : Fin (remaining ((S.datum frame programme).reader occurrence).expression + 1))
    (paid : GeneratedStepAt (O.law (originRoot frame) current (reader frame occurrence)) (state frame occurrence count.1))
    (selected : O.action (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1) = .inr paid) :
    HEq ((receiptAt frame occurrence).whole count)
      (stepLedgerEvolution (O.support (originRoot frame) current) paid.2) := by
  change HEq (O.whole (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)) _
  unfold RootGeneratedDebtActivationJointSource.OwnerFree.whole RootGeneratedDebtActivationJointSource.OwnerFree.wholeOf
  rw [selected]
  rfl

structure PaidAt (count : Fin (remaining ((S.datum frame programme).reader occurrence).expression + 1)) : Type u where
  private mk ::
  paid : GeneratedStepAt (O.law (originRoot frame) current (reader frame occurrence)) (state frame occurrence count.1)
  selected : (receiptAt frame occurrence).action count = .inr paid
  whole_heq : HEq ((receiptAt frame occurrence).whole count)
    (stepLedgerEvolution (O.support (originRoot frame) current) paid.2)
  strictDebit : (((receiptAt frame occurrence).whole count).destination
    (O.mathEntry (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1))).1.progressBudget <
      (O.mathEntry (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)).progressBudget

def generatePayment (count : Fin (remaining ((S.datum frame programme).reader occurrence).expression + 1)) :
    SourceOperationExecutionDebt.Settlement (state frame occurrence count.1) ⊕ PaidAt frame occurrence count := by
  cases selected : O.action (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1) with
  | inl settled => exact .inl settled
  | inr paid =>
      refine .inr ⟨paid, selected, paid_whole frame occurrence count paid selected, ?_⟩
      change ((O.whole (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1)).destination
        (O.mathEntry (originRoot frame) current (reader frame occurrence) (state frame occurrence count.1))).1.progressBudget < _
      unfold RootGeneratedDebtActivationJointSource.OwnerFree.whole RootGeneratedDebtActivationJointSource.OwnerFree.wholeOf
      rw [selected]
      exact (O.law (originRoot frame) current (reader frame occurrence)).step_budget_lt paid.2

def activePayment (count : Fin (remaining ((S.datum frame programme).reader occurrence).expression)) :
    PaidAt frame occurrence ⟨count.1, Nat.lt_trans count.2 (Nat.lt_succ_self _)⟩ := by
  let index : Fin (remaining ((S.datum frame programme).reader occurrence).expression + 1) :=
    ⟨count.1, Nat.lt_trans count.2 (Nat.lt_succ_self _)⟩
  cases selected : generatePayment frame occurrence index with
  | inr paid => exact paid
  | inl settled =>
      have zero := (O.law (originRoot frame) current (reader frame occurrence)).settlement_budget_zero settled
      have budget := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.budget
        (originRoot frame) current (reader frame occurrence) count.1
      change remaining (state frame occurrence count.1).1 = 0 at zero
      change remaining (state frame occurrence count.1).1 =
        remaining ((S.datum frame programme).reader occurrence).expression - count.1 at budget
      have below := count.2
      omega

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
