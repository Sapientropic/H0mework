import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RSourceStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.SuccessorConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Trace.Consumer

import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStepConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace C
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep.Canonical
 (ReadAt stageAt paidIndex active)
end C
namespace Step
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStep
 (sourceEnd read sourceData originalRead)
namespace Original
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStep.Original
 (old origin reader source_state)
end Original
end Step
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Current raw targetOf runtimeCurrent whole finiteVisit mathEntry)
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (target_state)
end Calc
namespace Consumer
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (targetState paid_history)
end Consumer
namespace Completion
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (state next_state)
end Completion
namespace Pay
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment
 (activePayment activeContinuation lineage entry destination_entry budget wellFounded no_refill debtCurrent current_state)
end Pay
end OF

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

private def nextValueAt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (index : Fin (remaining (OF.raw old origin reader).expression)) : Value () :=
  (OF.runtimeCurrent old origin reader (C.stageAt old origin reader index).next).1.eval
    (OF.raw old origin reader).environment

private structure NextReceipt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (value : Value ())
    (index : Fin (remaining (OF.raw old origin reader).expression)) where
  actualNext : OF.runtimeCurrent old origin reader (C.stageAt old origin reader index).next = state
  written : (OF.runtimeCurrent old origin reader (C.stageAt old origin reader index).next).1 = .const value
  output : nextValueAt old origin reader index = value
  destination : HEq ((OF.whole old origin reader (OF.finiteVisit old origin reader index.1).current).destination
    (OF.Pay.entry old origin reader index.1)).1 (OF.mathEntry old origin reader state)
  beforeBudget : (OF.Pay.debtCurrent old origin reader index.1).budget = 1
  afterBudget : (OF.Pay.debtCurrent old origin reader (index.1 + 1)).budget = 0
  claim : (OF.Pay.entry old origin reader index.1).claim = .inr (OF.raw old origin reader).expression
  rowNext : type_of% (OF.Pay.destination_entry old origin reader index.1)
  noRefill : type_of% (OF.Pay.no_refill old origin reader index.1)
  wellFounded : type_of% (OF.Pay.wellFounded old origin reader)
  factorizes : type_of% (C.stageAt old origin reader index).factorizes
  payment : type_of% (OF.Pay.activePayment old origin reader index)
  continuation : type_of% (OF.Pay.activeContinuation old origin reader index)
  lineage : type_of% (OF.Pay.lineage old origin reader index.1)

private structure WrittenReceipt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (value native written : Value ())
    (index : Fin (remaining (OF.raw old origin reader).expression))
    (sourceAdd : Value () → Value () → Value ())
    {H : Type} (project : Value () → H) (actionPoint : H) where
  next : NextReceipt old origin reader state value index
  sourceWriter : written = sourceAdd value native
  writeRead : sourceAdd (nextValueAt old origin reader index) native = written
  physicalPoint : H
  point : physicalPoint = project (sourceAdd (nextValueAt old origin reader index) native)
  source : physicalPoint = project written
  action : physicalPoint = actionPoint

private def consumeNext
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (cursor : Trace.Cursor state.2)
    (same : state = OF.Consumer.targetState old origin reader)
    (last : cursor.position + 1 = state.2.length)
    (value : Value ()) (endpoint : state.1 = .const value)
    {Physical : Type} (physical : Physical)
    (read : C.ReadAt old origin reader cursor same physical) :
    NextReceipt old origin reader state value (C.paidIndex old origin reader cursor same) :=
  let index := C.paidIndex old origin reader cursor same
  let stage := C.stageAt old origin reader index
  have position : index.1 = cursor.position :=
    Trace.Cursor.transfer_position (same.trans (OF.Calc.target_state old origin reader)) cursor
  have sourceLength : state.2.length = remaining (OF.raw old origin reader).expression :=
    (congrArg (fun candidate : OF.Current old origin reader => candidate.2.length) same).trans
      (OF.Consumer.paid_history old origin reader)
  have lastIndex : index.1 + 1 = remaining (OF.raw old origin reader).expression := by omega
  have activeNext : OF.Completion.state old origin reader (index.1 + 1) =
      SourceOperationExecutionDebt.advance (OF.Completion.state old origin reader index.1)
        (C.active old origin reader index).2.1 :=
    (OF.Completion.next_state old origin reader index.1).trans
      (congrArg (OF.targetOf old origin reader (OF.Completion.state old origin reader index.1))
        (C.active old origin reader index).2.2.down)
  have complete : OF.Completion.state old origin reader (index.1 + 1) =
      OF.Consumer.targetState old origin reader := by
    rw [lastIndex]
    exact (OF.Calc.target_state old origin reader).symm
  have actualNext : OF.runtimeCurrent old origin reader stage.next = state :=
    read.nextMath.trans (activeNext.symm.trans (complete.trans same.symm))
  have written : (OF.runtimeCurrent old origin reader stage.next).1 = .const value :=
    (congrArg (fun candidate : OF.Current old origin reader => candidate.1) actualNext).trans endpoint
  have output : nextValueAt old origin reader index = value :=
    (congrArg (fun expression : Expr Value Var () => expression.eval (OF.raw old origin reader).environment) written).trans rfl
  have nextVisit : (OF.finiteVisit old origin reader (index.1 + 1)).current = state :=
    (OF.Pay.current_state old origin reader (index.1 + 1)).trans (complete.trans same.symm)
  have destination := destination_state old origin reader index.1 state nextVisit
  have beforeBudget : (OF.Pay.debtCurrent old origin reader index.1).budget = 1 := by
    rw [OF.Pay.budget]
    have bound := index.2
    omega
  have afterBudget : (OF.Pay.debtCurrent old origin reader (index.1 + 1)).budget = 0 := by
    rw [OF.Pay.budget, lastIndex, Nat.sub_self]
  { actualNext := actualNext
    written := written
    output := output
    destination := destination
    beforeBudget := beforeBudget
    afterBudget := afterBudget
    claim := rfl
    rowNext := OF.Pay.destination_entry old origin reader index.1
    noRefill := OF.Pay.no_refill old origin reader index.1
    wellFounded := OF.Pay.wellFounded old origin reader
    factorizes := read.factorizes
    payment := OF.Pay.activePayment old origin reader index
    continuation := OF.Pay.activeContinuation old origin reader index
    lineage := OF.Pay.lineage old origin reader index.1 }

private def consumeWritten
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (cursor : Trace.Cursor state.2)
    (same : state = OF.Consumer.targetState old origin reader)
    (last : cursor.position + 1 = state.2.length)
    (value : Value ()) (endpoint : state.1 = .const value)
    {Physical : Type} (primitive : Physical)
    (read : C.ReadAt old origin reader cursor same primitive)
    (native written : Value ()) (sourceAdd : Value () → Value () → Value ())
    (write : written = sourceAdd value native)
    {H : Type} (project : Value () → H) (actionPoint : H)
    (action : project written = actionPoint) :
    WrittenReceipt old origin reader state value native written
      (C.paidIndex old origin reader cursor same) sourceAdd project actionPoint :=
  let next := consumeNext old origin reader state cursor same last value endpoint primitive read
  let full := sourceAdd (nextValueAt old origin reader (C.paidIndex old origin reader cursor same)) native
  have writeRead : full = written :=
    (congrArg (fun value : Value () => sourceAdd value native) next.output).trans write.symm
  let physicalPoint := project full
  have original : physicalPoint = project written := congrArg project writeRead
  { next := next
    sourceWriter := write
    writeRead := writeRead
    physicalPoint := physicalPoint
    point := rfl
    source := original
    action := original.trans action }

namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (programme actualCurrent oldPaid lowBase fullWrite)
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.FC (Value)
end FC
end B
namespace W
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Consumer
 (writtenValue written_raw_value written_physical_action)
end W
namespace AT
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
 (Value returned baseGroups originGroups runtimeGroups codeGroups valueGroups valueAddZeroClass valueAddZero nextGroups nextAddZeroClass nextAddZero)
namespace Code
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Code.F (BaseValue)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Code.F.C (Value Var)
end C
end F
end Code
end AT
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt actionReader occurrence current actual_calculation_state)
end R
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme oldPaid old_paid_const)
end WB
namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material (oldPaid material nativeValue updated_total born actual_writeback next_prefix_material next_prefix_result)
end M
private theorem prefixTotalRead
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (frame : A.M.Frame (Value := Value) (Var := Var) (sort := ()))
    (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
    (base : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := ())) :
    WB.oldPaid frame cfg + M.nativeValue frame cfg base =
      (R.actualMaterial frame cfg).raw.eval
        ((R.actualMaterial frame cfg).environment + (R.actualMaterial frame cfg).increment) := by
  have old : M.oldPaid frame cfg base = WB.oldPaid frame cfg :=
    congrArg (fun result : type_of% (R.actionResultAt frame cfg (R.occurrence frame cfg)) => result.2.2.1)
      (M.next_prefix_result frame cfg base)
  have actual := congrArg (fun material : type_of% (R.actualMaterial frame cfg) =>
    material.raw.eval (material.environment + material.increment)) (M.next_prefix_material frame cfg base)
  exact (congrArg (fun value => value + M.nativeValue frame cfg base) old.symm).trans
    ((M.updated_total frame cfg base).trans actual)

namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (born)
end SP
namespace P
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
 (pointAt actionAt originalPoint original_action original_positionGap read_admission packet_input_word)
end P

attribute [local instance] AT.baseGroups AT.originGroups AT.runtimeGroups AT.codeGroups AT.valueGroups AT.valueAddZeroClass AT.valueAddZero AT.nextGroups AT.nextAddZeroClass AT.nextAddZero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : A.M.Frame (Value := PairValue (AT.Code.F.BaseValue initial)) (Var := AT.Code.F.C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (AT.Code.F.BaseValue initial)) (PhysicalVar := AT.Code.F.C.Var) (sort := ()))
variable (before : Inventory (V := AT.Code.F.BaseValue initial) (X := AT.Code.F.C.Var) (s := ()))
variable (environment : Env (AT.Code.F.BaseValue initial) AT.Code.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (ActualNativeRelationTransport.AS.stockScalar frame base)))
local notation "sf" => SP.born frame base before environment admissions
local notation "receiver" => B.actualCurrent initial frame base before environment admissions observation nontrivial half sf
local notation "cfg" => B.programme initial frame base before environment admissions observation nontrivial half sf
local notation "mat" => R.actualMaterial receiver cfg


local elab "sourceWritten% " readStx:term ", " stateStx:term ", " lastStx:term
    ", " endpointStx:term ", " writtenStx:term
    ", " writeStx:term ", " projectStx:term ", " actionStx:term : term => do
  let read ← Lean.Elab.Term.elabTerm readStx none
  let state ← Lean.Elab.Term.elabTerm stateStx none
  let last ← Lean.Elab.Term.elabTerm lastStx none
  let endpoint ← Lean.Elab.Term.elabTerm endpointStx none
  let written ← Lean.Elab.Term.elabTerm writtenStx none
  let write ← Lean.Elab.Term.elabTerm writeStx none
  let project ← Lean.Elab.Term.elabTerm projectStx none
  let action ← Lean.Elab.Term.elabTerm actionStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let readType ← Lean.instantiateMVars (← Lean.Meta.inferType read)
  unless readType.getAppFn.constName? == some ``C.ReadAt do
    throwError "expected the existing canonical ReadAt"
  let a := readType.getAppArgs
  unless a.size == 16 do throwError "unexpected canonical ReadAt arity: {a.size}"
  let equation ← Lean.instantiateMVars (← Lean.Meta.inferType action)
  unless equation.getAppFn.constName? == some ``Eq do
    throwError "expected the original material physical action"
  let e := equation.getAppArgs
  let writeType ← Lean.instantiateMVars (← Lean.Meta.inferType write)
  let writeType := writeType.consumeMData
  unless writeType.getAppFn.constName? == some ``Eq && writeType.getAppArgs.size == 3 do
    throwError "expected the existing complete writer equation"
  let writerEquation := writeType.getAppArgs
  let rhs ← Lean.instantiateMVars writerEquation[2]!
  unless rhs.getAppFn.constName? == some ``HAdd.hAdd && rhs.getAppArgs.size == 6 do
    throwError "expected the original writer addition, head={rhs.getAppFn.constName?} arity={rhs.getAppArgs.size}"
  let addition := rhs.getAppArgs
  let sourceAdd := Lean.mkAppN rhs.getAppFn (addition.extract 0 4)
  let function ← Lean.Meta.mkConstWithFreshMVarLevels ``consumeWritten
  let arguments := #[a[0]!, a[1]!, a[2]!, a[3]!, a[5]!, a[6]!, a[7]!, a[9]!,
    state, a[12]!, a[13]!, last, addition[4]!, endpoint, a[14]!, a[15]!, read,
    addition[5]!, written, sourceAdd, write, e[0]!, project, e[2]!, action]
  let mut term := function
  for i in [:arguments.size] do
    Lean.Meta.checkApp term arguments[i]!
    term := Lean.mkApp term arguments[i]!
  return term

set_option backward.isDefEq.respectTransparency true in
private def consumeAt :=
  let ending := Step.sourceEnd observation nontrivial half initial frame base before environment admissions sf receiver
  let read := Step.read observation nontrivial half initial frame base before environment admissions sf receiver
  let project := fun value : AT.Value initial () =>
    (CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics.completeRSourceRead initial 2 0 value.1.1.1).1.1
  let written := W.writtenValue initial frame base before environment admissions observation nontrivial half sf receiver
  let write := (W.written_raw_value initial frame base before environment admissions observation nontrivial half sf receiver).trans
    (prefixTotalRead receiver cfg (B.lowBase initial frame base before environment admissions observation nontrivial half sf receiver)).symm
  let physicalPair := W.written_physical_action initial frame base before environment admissions observation nontrivial half sf receiver
  let originalPair := physicalPair.trans (congrArg
    (fun value : PairValue (AT.Code.F.BaseValue initial) () =>
      CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics.pairedPacking
        (CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics.R observation nontrivial half
          (CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics.totalBranches
            (CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics.completeRSourceRead initial 2 0 ((value,0),0)))))
    (CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.origin_full_value initial frame base before environment admissions))
  let action := congrArg (fun value : PairValue (PairValue AT.Code.F.C.Value) () => value.1.1) originalPair
  sourceWritten% read.2, (mat).state, ending.2.2.2.2,
    (WB.old_paid_const receiver cfg), written, write, project, action

local elab "pullReceipt% " receiptStx:term ", " sourceStx:term ", " identityStx:term : term => do
  let receipt ← Lean.Elab.Term.elabTerm receiptStx none
  let datum ← Lean.Elab.Term.elabTerm sourceStx none
  let identity ← Lean.Elab.Term.elabTerm identityStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType receipt)
  unless ty.getAppFn.constName? == some ``WrittenReceipt && ty.getAppArgs.size == 17 do
    throwError "expected the complete source-indexed written receipt"
  let equality ← Lean.instantiateMVars (← Lean.Meta.inferType identity)
  unless equality.getAppFn.constName? == some ``Eq && equality.getAppArgs.size == 3 do
    throwError "expected the complete source-data identity"
  let e := equality.getAppArgs
  let selector ← Lean.Meta.withLocalDeclD `datum e[0]! fun value => do
    let pair := Lean.mkProj ``PProd 1 (Lean.mkProj ``PProd 1 value)
    let index := Lean.mkProj ``Prod 1 (Lean.mkProj ``PProd 0 pair)
    Lean.Meta.mkLambdaFVars #[value] index
  let sourceType ← Lean.Meta.inferType datum
  unless (← Lean.Meta.isDefEq sourceType e[0]!) do throwError "source identity has a different complete carrier"
  let indexEq ← Lean.Meta.mkAppM ``congrArg #[selector, identity]
  let args := ty.getAppArgs
  let indexType ← Lean.Meta.inferType args[12]!
  let family ← Lean.Meta.withLocalDeclD `index indexType fun index =>
    Lean.Meta.mkLambdaFVars #[index] (Lean.mkAppN ty.getAppFn (args.set! 12 index))
  let reverse ← Lean.Meta.mkAppM ``Eq.symm #[indexEq]
  let resultEq ← Lean.Meta.mkAppM ``congrArg #[family, reverse]
  Lean.Meta.mkAppM ``Eq.mp #[resultEq, receipt]

private def consumeSourceAt
    (packet : { candidate : type_of% (Step.sourceData observation nontrivial half initial frame base before environment admissions sf receiver) //
      candidate = Step.sourceData observation nontrivial half initial frame base before environment admissions sf receiver }) :=
  let generated := consumeAt observation nontrivial half initial frame base before environment admissions
  pullReceipt% generated, packet.1, packet.2

universe u v w
private theorem read_cast {ι : Sort u} (F : ι → Sort v) {α : Sort w}
    (read : (i : ι) → F i → α) {i j : ι} (same : i=j) (source : F i) :
    read j (Eq.mp (congrArg F same) source) = read i source := by
  cases same
  rfl

namespace KSide
open private InputAt from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.KConsumer
abbrev Family {α : Type} (expected : α) (initial : Nat) (X : Unit → Type) := InputAt expected initial X
attribute [local instance] SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer.baseGroups

def nextValue {α : Type} (expected : α) (initial : Nat) {X : Unit → Type}
    (source : Family expected initial X) :=
  SourceInventoryExecutionFeed.SourceWordNative.nextFullValue
    source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2.1

theorem nextValue_cast {α : Type} (expected : α) (initial : Nat) {Y Z : Unit → Type}
    (same : Y=Z) (source : Family expected initial Y) :
    nextValue expected initial (Eq.mp (congrArg (Family expected initial) same) source) =
      nextValue expected initial source :=
  read_cast (Family expected initial) (fun _ value => nextValue expected initial value) same source
end KSide
namespace KC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer (ResultAt)
end KC

attribute [local irreducible] KC.ResultAt

local elab "inputNat% " actualStx:term : term => do
  let actual ← Lean.Elab.Term.elabTerm actualStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let actual ← Lean.instantiateMVars actual
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType actual)
  unless ty.getAppFn.constName? == some ``KC.ResultAt do
    throwError "expected the existing source-indexed KConsumer.ResultAt"
  let args := ty.getAppArgs
  unless args.size == 11 do throwError "unexpected existing ResultAt source arity"
  let mut cast := args[5]!
  for _ in [0:12] do
    if cast.getAppFn.constName? == some ``Eq.mp then break
    match cast with
    | .proj _ _ value => cast := value
    | .letE _ _ value body _ => cast := body.instantiate1 value
    | .mdata _ value => cast := value
    | .app fn value =>
      unless fn.getAppFn.constName? == some ``Sigma.fst || fn.getAppFn.constName? == some ``Sigma.snd do
        throwError "expected the existing whole source cast below the frame projection"
      cast := value
    | _ => throwError "expected the existing frame projection of the whole cast"
  unless cast.getAppFn.constName? == some ``Eq.mp && cast.getAppArgs.size == 4 do
    throwError "expected the existing whole Eq.mp source cast"
  let castArgs := cast.getAppArgs
  let mut proof := castArgs[2]!
  for _ in [0:4] do
    if proof.getAppFn.constName? == some ``congrArg then break
    let .const name levels := proof.getAppFn | throwError "expected a stored transport proof"
    let info ← Lean.getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "stored transport proof has no body"
    let body := value.instantiateLevelParams info.levelParams levels
    proof := (Lean.mkAppN body proof.getAppArgs).headBeta
  unless proof.getAppFn.constName? == some ``congrArg && proof.getAppArgs.size == 6 do
    throwError "expected the original congrArg; head={proof.getAppFn.constName?}, arity={proof.getAppArgs.size}"
  let transport := proof.getAppArgs
  let family := transport[4]!
  let knownFamily ← Lean.getConstInfoDefn ``KSide.Family
  let mut familyBody := knownFamily.value
  for _ in [0:4] do
    match familyBody with
    | .lam _ _ body _ => familyBody := body
    | _ => break
  unless family.getAppFn.constName? == familyBody.getAppFn.constName? && family.getAppArgs.size == 3 do
    throwError "expected the existing six-leg KConsumer source family"
  let familyArgs := family.getAppArgs
  let law ← Lean.Meta.mkConstWithFreshMVarLevels ``KSide.nextValue_cast
  return Lean.mkAppN law #[familyArgs[0]!,familyArgs[1]!,familyArgs[2]!,
    transport[2]!,transport[3]!,transport[5]!,castArgs[3]!]

local elab "sourceRead% " actualStx:term ", " packetStx:term : term => do
  let actual ← Lean.Elab.Term.elabTerm actualStx none
  let packet ← Lean.Elab.Term.elabTerm packetStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType actual)
  unless ty.getAppFn.constName? == some ``KC.ResultAt && ty.getAppArgs.size == 11 do
    throwError "expected the original KConsumer source-indexed result"
  let a := ty.getAppArgs
  let consumer ← Lean.Meta.mkConstWithFreshMVarLevels ``consumeSourceAt
  let arguments := #[a[0]!,a[1]!,a[2]!,a[4]!,a[5]!,a[6]!,a[7]!,a[8]!,a[9]!,packet]
  let mut term := consumer
  for i in [:arguments.size] do
    Lean.Meta.checkApp term arguments[i]!
    term := Lean.mkApp term arguments[i]!
  return term

namespace Physics
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceConsumer.Physics
 (R totalBranches completeRSourceRead)
end Physics
namespace KW
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite (originalNative)
end KW
namespace Dynamics
export CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics (factory)
end Dynamics
namespace NativeSigma
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma
 (NativeFactory NativePacket collapseNative)
end NativeSigma
namespace NatAS
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance.AS (bornAfterNative)
end NatAS
namespace WordNative
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
 (full_value)
end WordNative
namespace Successor
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceSuccessorConsumer
 (actual_action_step independent_original_Gram)
end Successor

private def rPoint (value : BurnolL2) : BurnolL2 := Physics.R observation nontrivial half value

private def rTotal (branches : PairValue (PairValue AT.Code.F.C.Value) ()) : BurnolL2 :=
  Physics.R observation nontrivial half (Physics.totalBranches branches)

private def collapsedPoint (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) :=
  fun value => rTotal observation nontrivial half
    (NativeSigma.collapseNative factory (NatAS.bornAfterNative native) value)

private def pointOfWord (value : PairValue (AT.Code.F.BaseValue initial) ()) : BurnolL2 :=
  rTotal observation nontrivial half (Physics.completeRSourceRead initial 2 0 ((value,0),0))

private def constrainAt
    {N : WorldRelationNetwork} {V : Vocabulary}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()))
    (state : OF.Current old origin reader) (value native written : Value ())
    (index : Fin (remaining (OF.raw old origin reader).expression))
    (sourceAdd : Value () → Value () → Value ())
    (project : Value () → BurnolL2) (actionPoint : BurnolL2)
    (receipt : WrittenReceipt old origin reader state value native written index sourceAdd project actionPoint)
    (original next : BurnolL2) (link : actionPoint = original)
    (gap : original ∈ locallyConstantFace burnolUnscaledCommonGapRadius)
    (successor : original = next) (nonzero : original ≠ 0) :=
  have same : receipt.physicalPoint = original := receipt.action.trans link
  have actualGap : receipt.physicalPoint ∈ locallyConstantFace burnolUnscaledCommonGapRadius :=
    same ▸ gap
  have actualNext : receipt.physicalPoint = next := same.trans successor
  have actualNonzero : receipt.physicalPoint ≠ 0 := fun zero => nonzero (same.symm.trans zero)
  PProd.mk receipt (And.intro same (And.intro actualGap (And.intro actualNext actualNonzero)))

local elab "physicalRead% " actualStx:term ", " receiptStx:term ", " ordinalStx:term : term => do
  let actual ← Lean.Elab.Term.elabTerm actualStx none
  let receipt ← Lean.Elab.Term.elabTerm receiptStx none
  let ordinal ← Lean.Elab.Term.elabTerm ordinalStx none
  let naturality ← Lean.Elab.Term.elabTerm (← `(inputNat% $actualStx)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let sourceType ← Lean.Meta.whnf (← Lean.Meta.inferType actual)
  unless sourceType.getAppFn.constName? == some ``KC.ResultAt && sourceType.getAppArgs.size == 11 do
    throwError "expected the actual original K source result"
  let a := sourceType.getAppArgs
  let naturalityType ← Lean.Meta.whnf (← Lean.Meta.inferType naturality)
  let n := naturalityType.getAppArgs
  unless naturalityType.getAppFn.constName? == some ``Eq && n.size == 3 do
    throwError "expected the complete source input naturality"
  let wordMap ← Lean.Meta.mkAppM ``pointOfWord #[a[0]!,a[1]!,a[2]!,a[4]!]
  let wordRead ← Lean.Meta.mkAppM ``congrArg #[wordMap,naturality]
  let sourceRead := n[2]!
  unless sourceRead.getAppFn.constName? == some ``KSide.nextValue && sourceRead.getAppArgs.size == 5 do
    throwError "expected the existing six-leg source read"
  let source := sourceRead.getAppArgs[4]!.headBeta
  unless source.getAppFn.constName? == some ``Sigma.mk && source.getAppArgs.size == 4 do
    throwError "expected the literal existing source tuple; head={source.getAppFn.constName?} arity={source.getAppArgs.size}"
  let sourceFrame := source.getAppArgs[2]!.headBeta
  unless sourceFrame.getAppFn.constName? == some ``ActualCofinalSourceAction.selected && sourceFrame.getAppArgs.size == 7 do
    throwError "expected the actual selected factory/packet; head={sourceFrame.getAppFn.constName?}, arity={sourceFrame.getAppArgs.size}"
  let selected := sourceFrame.getAppArgs
  let factory := selected[selected.size - 2]!
  let packet := selected[selected.size - 1]!
  unless packet.getAppFn.constName? == some ``NatAS.bornAfterNative && packet.getAppArgs.size ≥ 1 do
    throwError "expected the original source native birth"
  let native := packet.getAppArgs[packet.getAppArgs.size - 1]!
  let admission ← Lean.Meta.mkAppM ``P.read_admission #[factory,packet,n[2]!]
  let totalMap ← Lean.Meta.mkAppM ``rTotal #[a[0]!,a[1]!,a[2]!]
  let admitted ← Lean.Meta.mkAppM ``congrArg #[totalMap,admission]
  let inputWord ← Lean.Meta.mkAppM ``WordNative.full_value #[factory,native]
  let collapsed ← Lean.Meta.mkAppM ``collapsedPoint #[a[0]!,a[1]!,a[2]!,factory,native]
  let originalInput ← Lean.Meta.mkAppM ``congrArg #[collapsed,inputWord]
  let originalAction ← Lean.Meta.mkAppM ``P.original_action #[a[0]!,a[1]!,a[2]!,a[3]!,ordinal]
  let reverse ← Lean.Meta.mkAppM ``Eq.symm #[originalAction]
  let link1 ← Lean.Meta.mkAppM ``Eq.trans #[wordRead,admitted]
  let link2 ← Lean.Meta.mkAppM ``Eq.trans #[link1,originalInput]
  let link ← Lean.Meta.mkAppM ``Eq.trans #[link2,reverse]
  let step ← Lean.Meta.mkAppM ``Successor.actual_action_step #[a[0]!,a[1]!,a[2]!,a[3]!,ordinal]
  let stepType ← Lean.Meta.whnf (← Lean.Meta.inferType step)
  let stepArgs := stepType.getAppArgs
  let gap ← Lean.Meta.mkAppM ``P.original_positionGap #[a[0]!,a[1]!,a[2]!,a[3]!,ordinal]
  let nonzero ← Lean.Meta.mkAppM ``Successor.independent_original_Gram #[a[0]!,a[1]!,a[2]!,a[3]!,ordinal]
  let receiptType ← Lean.Meta.whnf (← Lean.Meta.inferType receipt)
  unless receiptType.getAppFn.constName? == some ``WrittenReceipt && receiptType.getAppArgs.size == 17 do
    throwError "expected the complete actual-index written receipt"
  let r := receiptType.getAppArgs
  let consumer ← Lean.Meta.mkConstWithFreshMVarLevels ``constrainAt
  let args := (r.extract 0 14) ++ #[r[15]!,r[16]!,receipt,stepArgs[1]!,stepArgs[2]!,link,gap,step,nonzero]
  let mut term := consumer
  for i in [:args.size] do
    Lean.Meta.checkApp term args[i]!
    term := Lean.mkApp term args[i]!
  return term

set_option backward.isDefEq.respectTransparency true in
private def FixedResultAt (depth ordinal : Nat) :=
  Σ' actual : type_of% (Step.originalRead observation nontrivial half depth ordinal),
    PProd (actual = Step.originalRead observation nontrivial half depth ordinal)
      (type_of% (let written := sourceRead% actual.2.2.1, actual.2.2.2.2
        physicalRead% actual.2.2.1, written, ordinal))

attribute [local irreducible] FixedResultAt

set_option backward.isDefEq.respectTransparency true in
opaque originalRead (depth ordinal : Nat) : FixedResultAt observation nontrivial half depth ordinal := by
  unfold FixedResultAt
  let actual := Step.originalRead observation nontrivial half depth ordinal
  let written := sourceRead% actual.2.2.1, actual.2.2.2.2
  let consumed := physicalRead% actual.2.2.1, written, ordinal
  exact ⟨actual,rfl,consumed⟩

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStepConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
