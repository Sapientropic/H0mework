import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteResidualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteStepPayment

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion BurnolPhysicalState

namespace Residual
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteResidualSource (originalRead)
end Residual
namespace BS
export OriginalKCoefficientBSelfCalculation (Value Var Base reader result cotestCode cotestAction coordinate fixedShift result_history)
end BS
namespace Prior
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep.Canonical
  (read stageAt paidIndex active)
end Prior
namespace BFPay
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStepPayment (read)
end BFPay
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Current raw nextState targetOf runtimeCurrent whole finiteVisit mathEntry)
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (target_state)
end Calc
namespace Consumer
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (targetState target_expression value paid_history)
end Consumer
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (state next_state)
end C
namespace Pay
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment
  (activePayment activeContinuation lineage entry destination_entry budget wellFounded no_refill debtCurrent current_state)
end Pay
end OF
namespace Current
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer.InstalledRead
  (selfCalculation self_calculation_source)
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance (originalMaterial)
end K
end Current

namespace LastBilinear
universe u
variable {Value Var : Unit → Type u} [∀ target, AddCommGroup (Value target)]
variable {environment : Env Value Var}
variable (operation : Value () →+ Value () →+ Value ())

inductive Interleaving :
    {left right terminal : Expr Value Var ()} → {leftValue rightValue : Value ()} →
      Trace environment (.bilinear operation left right) terminal →
      Trace environment left (.const leftValue) → Trace environment right (.const rightValue) → Type u
  | last (leftValue rightValue : Value ()) : Interleaving
      (.single (Step.bilinearConst operation leftValue rightValue))
      (.nil (.const leftValue)) (.nil (.const rightValue))
  | left {left middle right terminal : Expr Value Var ()} {leftValue rightValue : Value ()}
      (paid : Step environment left middle)
      {tail : Trace environment (.bilinear operation middle right) terminal}
      {leftTrace : Trace environment middle (.const leftValue)}
      {rightTrace : Trace environment right (.const rightValue)}
      (rest : Interleaving tail leftTrace rightTrace) :
      Interleaving (.cons (.bilinearLeft operation paid) tail) (.cons paid leftTrace) rightTrace
  | right {left before after terminal : Expr Value Var ()} {leftValue rightValue : Value ()}
      (paid : Step environment before after)
      {tail : Trace environment (.bilinear operation left after) terminal}
      {leftTrace : Trace environment left (.const leftValue)}
      {rightTrace : Trace environment after (.const rightValue)}
      (rest : Interleaving tail leftTrace rightTrace) :
      Interleaving (.cons (.bilinearRight operation paid) tail) leftTrace (.cons paid rightTrace)

structure At {left right : Expr Value Var ()} {total : Value ()}
    (actual : Trace environment (.bilinear operation left right) (.const total)) where
  cursor : Trace.Cursor actual
  leftValue : Value ()
  rightValue : Value ()
  leftTrace : Trace environment left (.const leftValue)
  rightTrace : Trace environment right (.const rightValue)
  interleaving : Interleaving operation actual leftTrace rightTrace
  physical : HEq cursor.paidStep (Step.bilinearConst (environment := environment) operation leftValue rightValue)
  endpoint : total = operation leftValue rightValue
  position : cursor.position + 1 = actual.length

private def read {operation : Value () →+ Value () →+ Value ()}
    {left right : Expr Value Var ()} {total : Value ()}
    (actual : Trace environment (.bilinear operation left right) (.const total)) : At operation actual :=
  match actual with
  | .cons (.bilinearConst _ leftValue rightValue) (.nil _) =>
      ⟨.here (.bilinearConst operation leftValue rightValue) (.nil _),
        leftValue, rightValue, .nil _, .nil _, .last leftValue rightValue, HEq.rfl, rfl, rfl⟩
  | .cons (.bilinearConst _ _ _) (.cons impossible _) => nomatch impossible
  | .cons (.bilinearLeft _ paid) tail =>
      let inside := read tail
      ⟨.there (.bilinearLeft operation paid) tail inside.cursor,
        inside.leftValue, inside.rightValue, .cons paid inside.leftTrace, inside.rightTrace,
        .left paid inside.interleaving, inside.physical, inside.endpoint, by
          change inside.cursor.position + 1 + 1 = 1 + tail.length
          have last := inside.position
          omega⟩
  | .cons (.bilinearRight _ paid) tail =>
      let inside := read tail
      ⟨.there (.bilinearRight operation paid) tail inside.cursor,
        inside.leftValue, inside.rightValue, inside.leftTrace, .cons paid inside.rightTrace,
        .right paid inside.interleaving, inside.physical, inside.endpoint, by
          change inside.cursor.position + 1 + 1 = 1 + tail.length
          have last := inside.position
          omega⟩

end LastBilinear

private theorem result_state
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : {current : V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    {current : V.Current} (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.1 =
      OF.Consumer.targetState old current (fun _ => reader occurrence) := rfl

private theorem result_endpoint
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : {current : V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    {current : V.Current} (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.1.1 =
      .const (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.2.1 :=
  OF.Consumer.target_expression old current (fun _ => reader occurrence)

private theorem destination_state
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (count : Nat) (state : OF.Current old origin reader)
    (same : (OF.finiteVisit old origin reader (count + 1)).current = state) :
    HEq ((OF.whole old origin reader (OF.finiteVisit old origin reader count).current).destination
      (OF.Pay.entry old origin reader count)).1 (OF.mathEntry old origin reader state) :=
  (heq_of_eq (OF.Pay.destination_entry old origin reader count)).trans
    (congr_arg_heq (OF.mathEntry old origin reader) same)

private def finalRead
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (cursor : Trace.Cursor state.2)
    (same : state = OF.Consumer.targetState old origin reader)
    (last : cursor.position + 1 = state.2.length)
    (value : Value ()) (endpoint : state.1 = .const value)
    {Physical : Type} {physical : Physical} (physicalSource : HEq cursor.paidStep physical) :=
  let exactState : (⟨state.1, state.2⟩ : OF.Current old origin reader) =
      OF.Consumer.targetState old origin reader := (Sigma.eta state).trans same
  let read := Prior.read old origin reader cursor exactState physicalSource
  let index := Prior.paidIndex old origin reader cursor exactState
  let stage := Prior.stageAt old origin reader index
  have position : index.1 = cursor.position :=
    Trace.Cursor.transfer_position (exactState.trans (OF.Calc.target_state old origin reader)) cursor
  have sourceLength : state.2.length = remaining (OF.raw old origin reader).expression :=
    (congrArg (fun candidate : OF.Current old origin reader => candidate.2.length) same).trans
      (OF.Consumer.paid_history old origin reader)
  have lastIndex : index.1 + 1 = remaining (OF.raw old origin reader).expression := by omega
  have activeNext : OF.C.state old origin reader (index.1 + 1) =
      SourceOperationExecutionDebt.advance (OF.C.state old origin reader index.1)
        (Prior.active old origin reader index).2.1 :=
    (OF.C.next_state old origin reader index.1).trans
      (congrArg (OF.targetOf old origin reader (OF.C.state old origin reader index.1))
        (Prior.active old origin reader index).2.2.down)
  have complete : OF.C.state old origin reader (index.1 + 1) =
      OF.Consumer.targetState old origin reader := by
    rw [lastIndex]
    exact (OF.Calc.target_state old origin reader).symm
  have actualNext : OF.runtimeCurrent old origin reader stage.next = state :=
    read.2.nextMath.trans (activeNext.symm.trans (complete.trans same.symm))
  have written : (OF.runtimeCurrent old origin reader stage.next).1 = .const value :=
    (congrArg (fun candidate : OF.Current old origin reader => candidate.1) actualNext).trans endpoint
  have nextVisit : (OF.finiteVisit old origin reader (index.1 + 1)).current = state :=
    (OF.Pay.current_state old origin reader (index.1 + 1)).trans (complete.trans same.symm)
  have destination := destination_state old origin reader index.1 state nextVisit
  have beforeBudget : (OF.Pay.debtCurrent old origin reader index.1).budget = 1 := by
    rw [OF.Pay.budget]
    have bound := index.2
    omega
  have afterBudget : (OF.Pay.debtCurrent old origin reader (index.1 + 1)).budget = 0 := by
    rw [OF.Pay.budget, lastIndex, Nat.sub_self]
  let payment := OF.Pay.activePayment old origin reader index
  let continuation := OF.Pay.activeContinuation old origin reader index
  let lineage := OF.Pay.lineage old origin reader index.1
  PProd.mk (PProd.mk read (PProd.mk payment (PProd.mk continuation lineage)))
    (And.intro actualNext (And.intro written (And.intro destination (And.intro beforeBudget (And.intro afterBudget
      (And.intro (show (OF.Pay.entry old origin reader index.1).claim =
        .inr (OF.raw old origin reader).expression from rfl)
        (And.intro (OF.Pay.destination_entry old origin reader index.1)
          (And.intro (OF.Pay.no_refill old origin reader index.1) (OF.Pay.wellFounded old origin reader)))))))))

private theorem writtenNonzero {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    {expression : Expr Value Var ()} {value : Value ()}
    (written : expression = .const value) (nonzero : value ≠ 0) : expression ≠ .const 0 := by
  intro zero
  exact nonzero (Expr.const.inj (written.symm.trans zero))


private def retargetBundle
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader)
    (value : Value ()) (endpoint : state.1 = .const value)
    (actualTrace : Trace (OF.raw old origin reader).environment
      (OF.raw old origin reader).expression (.const value))
    (source : (⟨.const value, actualTrace⟩ : OF.Current old origin reader) = state)
    (same : state = OF.Consumer.targetState old origin reader)
    (actualCursor : Trace.Cursor actualTrace)
    (last : actualCursor.position + 1 = actualTrace.length)
    {Physical : Type} {physical : Physical} (physicalSource : HEq actualCursor.paidStep physical)
    (residual : Value ()) (nonzero : value ≠ 0) (value_source : value = residual) :=
  let cursor := Trace.Cursor.transfer source actualCursor
  have position : cursor.position + 1 = state.2.length :=
    (congrArg (fun count => count + 1) (Trace.Cursor.transfer_position source actualCursor)).trans
      (last.trans (congrArg (fun candidate : OF.Current old origin reader => candidate.2.length) source))
  have physical := (Trace.Cursor.transfer_step source actualCursor).trans physicalSource
  let read := finalRead old origin reader state cursor same position value endpoint physical
  have actualNonzero := writtenNonzero (Value := Value) (Var := Var) read.2.2.1 nonzero
  have writtenResidual := read.2.2.1.trans
    (congrArg (fun result : Value () => (Expr.const result : Expr Value Var ())) value_source)
  PProd.mk read (And.intro actualNonzero writtenResidual)

private def RetargetResultAt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader)
    (value : Value ()) (endpoint : state.1 = .const value)
    (actualTrace : Trace (OF.raw old origin reader).environment
      (OF.raw old origin reader).expression (.const value))
    (source : (⟨.const value, actualTrace⟩ : OF.Current old origin reader) = state)
    (same : state = OF.Consumer.targetState old origin reader)
    (actualCursor : Trace.Cursor actualTrace)
    (last : actualCursor.position + 1 = actualTrace.length)
    {Physical : Type} {physical : Physical} (physicalSource : HEq actualCursor.paidStep physical)
    (residual : Value ()) (nonzero : value ≠ 0) (value_source : value = residual) : Type _ :=
  type_of% (retargetBundle old origin reader state value endpoint actualTrace source same actualCursor last physicalSource residual nonzero value_source)

private def retargetRead
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader)
    (value : Value ()) (endpoint : state.1 = .const value)
    (actualTrace : Trace (OF.raw old origin reader).environment
      (OF.raw old origin reader).expression (.const value))
    (source : (⟨.const value, actualTrace⟩ : OF.Current old origin reader) = state)
    (same : state = OF.Consumer.targetState old origin reader)
    (actualCursor : Trace.Cursor actualTrace)
    (last : actualCursor.position + 1 = actualTrace.length)
    {Physical : Type} {physical : Physical} (physicalSource : HEq actualCursor.paidStep physical)
    (residual : Value ()) (nonzero : value ≠ 0) (value_source : value = residual) : RetargetResultAt old origin reader state value endpoint actualTrace source same actualCursor last physicalSource residual nonzero value_source :=
  retargetBundle old origin reader state value endpoint actualTrace source same actualCursor last physicalSource residual nonzero value_source

namespace Source
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
variable {current : CanonicalUnitArithmeticRoot.V.Current}
variable (occurrence : BS.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)
variable (self : type_of% (BS.result observation nontrivial half occurrence))
variable (source : self = BS.result observation nontrivial half occurrence)

include source in
private theorem endpoint : self.2.1.1 = .const self.2.2.1 :=
  Eq.mpr (congrArg (fun candidate : type_of% self =>
    candidate.2.1.1 = .const candidate.2.2.1) source)
    (result_endpoint BS.Base (BS.reader observation nontrivial half) occurrence)

private def actualTrace : Trace (BS.reader observation nontrivial half occurrence).environment
    (BS.reader observation nontrivial half occurrence).expression
    (.const self.2.2.1) :=
  Eq.mp (congrArg (fun terminal => Trace (BS.reader observation nontrivial half occurrence).environment
    (BS.reader observation nontrivial half occurrence).expression terminal)
    (endpoint observation nontrivial half occurrence self source))
    self.2.1.2

private theorem materialState :
    (⟨.const self.2.2.1,
      actualTrace observation nontrivial half occurrence self source⟩ :
      OF.Current BS.Base current (fun _ => BS.reader observation nontrivial half occurrence)) =
    self.2.1 :=
  (Trace.Cursor.endpoint_state self.2.1.2
    (endpoint observation nontrivial half occurrence self source)).trans
    (Sigma.eta self.2.1)

private def last :=
  LastBilinear.read (Value := BS.Value) (Var := BS.Var)
    (environment := (BS.reader observation nontrivial half occurrence).environment)
    (operation := BS.cotestAction) (actualTrace observation nontrivial half occurrence self source)

private def read (residual : BS.Value ()) (nonzero : self.2.2.1 ≠ 0)
    (value_source : self.2.2.1 = residual) :=
  let actual := last observation nontrivial half occurrence self source
  PProd.mk actual
    (retargetRead BS.Base current (Value := BS.Value) (Var := BS.Var)
      (fun _ => BS.reader observation nontrivial half occurrence)
      self.2.1
      self.2.2.1
      (endpoint observation nontrivial half occurrence self source)
      (actualTrace observation nontrivial half occurrence self source)
      (materialState observation nontrivial half occurrence self source)
      ((congrArg (fun candidate : type_of% self => candidate.2.1) source).trans
        (result_state BS.Base (BS.reader observation nontrivial half) occurrence))
      actual.cursor actual.position actual.physical residual nonzero value_source)

end Source


variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

namespace Maternal
variable (maternal : type_of% (Current.K.originalMaterial observation nontrivial half depth))
variable (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down))
variable (self : type_of% (Current.selfCalculation observation nontrivial half depth maternal))
variable (source : self = BS.result observation nontrivial half maternal.1)
variable (nonzero : self.2.2.1 ≠ 0)
variable (value : self.2.2.1 = -receipt.1.fixedResidual • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed)

def bundleAt :=
  let write := Source.read observation nontrivial half maternal.1 self source
    (-receipt.1.fixedResidual • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed) nonzero value
  let bfPaid := BFPay.read observation nontrivial half maternal.1
  PProd.mk write bfPaid

def ResultAt := type_of% (bundleAt observation nontrivial half depth maternal receipt self source nonzero value)
def readAt : ResultAt observation nontrivial half depth maternal receipt self source nonzero value :=
  bundleAt observation nontrivial half depth maternal receipt self source nonzero value
attribute [local irreducible] ResultAt
end Maternal

local elab "writeMaternal% " observation:term ", " nontrivial:term ", " half:term ", " depth:term
    ", " maternal:term ", " receipt:term ", " self:term ", " nonzero:term ", " value:term : term => do
  let arguments ← #[observation, nontrivial, half, depth, maternal, receipt, self, nonzero, value].mapM
    (fun stx => Lean.Elab.Term.elabTerm stx none)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let arguments ← arguments.mapM Lean.instantiateMVars
  let sourceFn ← Lean.Meta.mkConstWithFreshMVarLevels ``Current.self_calculation_source
  let source := Lean.mkAppN sourceFn arguments[:5].toArray
  let readFn ← Lean.Meta.mkConstWithFreshMVarLevels ``Maternal.readAt
  return Lean.mkAppN readFn (arguments[:7].toArray ++ #[source, arguments[7]!, arguments[8]!])

private def OriginalResult : Sort _ :=
  Σ' actual : type_of% (Residual.originalRead observation nontrivial half depth ordinal),
    PProd (actual = Residual.originalRead observation nontrivial half depth ordinal)
      (type_of% (
    let original := Residual.originalRead observation nontrivial half depth ordinal
    let current := original.1.1
    let maternal := current.1.1.1.1
    let receipt := current.1.1.1.2.1
    writeMaternal% observation, nontrivial, half, depth, maternal, receipt, current.1.2.2,
      original.2.2.2.2.2.2, current.2.2.2.2.1))

/-- The actual faithful residual is written by its own final cotest stage. -/
opaque originalRead : OriginalResult observation nontrivial half depth ordinal := by
  unfold OriginalResult
  exact ⟨Residual.originalRead observation nontrivial half depth ordinal, ⟨rfl, (
    let original := Residual.originalRead observation nontrivial half depth ordinal
    let current := original.1.1
    let maternal := current.1.1.1.1
    let receipt := current.1.1.1.2.1
    writeMaternal% observation, nontrivial, half, depth, maternal, receipt, current.1.2.2,
      original.2.2.2.2.2.2, current.2.2.2.2.1)⟩⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBSelfResidualWrite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
