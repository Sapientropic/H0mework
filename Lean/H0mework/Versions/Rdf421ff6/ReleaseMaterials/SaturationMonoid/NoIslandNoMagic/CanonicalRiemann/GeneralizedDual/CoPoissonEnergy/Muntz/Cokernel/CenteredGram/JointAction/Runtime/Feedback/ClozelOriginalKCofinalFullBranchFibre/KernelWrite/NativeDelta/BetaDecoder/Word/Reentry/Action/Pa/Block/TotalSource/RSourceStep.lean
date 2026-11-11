import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Trace.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.KConsumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStep
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace C
export CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep.Canonical (read ReadAt)
end C
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (programme actualCurrent code actualTrace oldPaid material_raw)
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.FC (Value)
end FC
end B
namespace AT
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
 (literal_shape returned)
namespace Code
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Code (sourceCode)
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Code.F (BaseValue)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Code.F.C (Value Var)
end C
end F
end Code
namespace Origin
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.Origin (sourceRaw)
end Origin
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
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader actionResultAt occurrence current actual_calculation_state)
end R
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (old_paid_const)
end WB
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Current raw)
namespace Consumer
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (targetState)
end Consumer
end OF
namespace KC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer (ResultAt readAt originalRead)
namespace H
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer.H (Carrier)
end H
namespace K
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer.K (originalOutcome)
end K
end KC
namespace SP
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice (born)
end SP

private def linearEnd {Sorts : Type} {V X : Sorts → Type}
    [∀ s, AddCommGroup (V s)] {s : Sorts} {environment : Env V X}
    {expression : Expr V X s} (state : SourceOperationExecutionDebt.State environment expression)
    {operation : V s →+ V s} {body : Expr V X s}
    (shape : expression = .linear operation body) (value : V s)
    (endpoint : state.1 = .const value) :
    Σ input : V s, Σ cursor : Trace.Cursor state.2,
      PProd (PLift (HEq cursor.paidStep (Step.linearConst (environment := environment) operation input)))
        (operation input = value ∧ cursor.position+1 = state.2.length) := by
  cases shape
  let trace := Eq.mp (congrArg (fun terminal => Trace environment (.linear operation body) terminal) endpoint) state.2
  let cut := trace.splitLinear
  let selected := cut.interleaving.lastCursor
  let same := Trace.Cursor.endpoint_state state.2 endpoint
  let original := Trace.Cursor.transfer same selected
  have source : cut.input = body.eval environment := completed_trace_value environment cut.trace
  have output : operation (body.eval environment) = value := trace.sound
  have last : original.position+1 = state.2.length := by
    calc
      original.position+1 = selected.position+1 := congrArg (fun n => n+1) (Trace.Cursor.transfer_position same selected)
      _ = cut.trace.length+1 := congrArg (fun n => n+1) cut.interleaving.lastCursor_position
      _ = trace.length := cut.length_eq.symm
      _ = state.2.length := congrArg (fun result : SourceOperationExecutionDebt.State environment (.linear operation body) => result.2.length) same
  exact ⟨cut.input, original, ⟨(Trace.Cursor.transfer_step same selected).trans cut.interleaving.lastCursor_step⟩,
    (congrArg operation source).trans output, last⟩

namespace Original
variable {Sorts : Type} {V X : Sorts → Type} [∀ s, AddCommGroup (V s)] {s : Sorts}
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := s))
abbrev old := (S.baseRoot frame cfg).toAuthoritativeRoot
abbrev origin := R.current frame cfg
abbrev reader := fun (_ : (old frame cfg).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (origin frame cfg)) =>
  R.actionReader frame cfg (R.occurrence frame cfg)

theorem source_state : (R.actualMaterial frame cfg).state =
    OF.Consumer.targetState (old frame cfg) (origin frame cfg) (reader frame cfg) :=
  R.actual_calculation_state frame cfg
end Original

attribute [local instance]
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.baseGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.originGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.runtimeGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.codeGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.valueGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.valueAddZeroClass
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.valueAddZero
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.nextGroups
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.nextAddZeroClass
 SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace.nextAddZero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : A.M.Frame (Value := PairValue (AT.Code.F.BaseValue initial)) (Var := AT.Code.F.C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (AT.Code.F.BaseValue initial)) (PhysicalVar := AT.Code.F.C.Var) (sort := ()))
variable (before : Inventory (V := AT.Code.F.BaseValue initial) (X := AT.Code.F.C.Var) (s := ()))
variable (environment : Env (AT.Code.F.BaseValue initial) AT.Code.F.C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (ActualNativeRelationTransport.AS.stockScalar frame base)))
variable (sourceFrame : A.M.Frame (Value := PairValue (PairValue (AT.Code.F.BaseValue initial))) (Var := AT.Code.F.C.Var) (sort := ()))
variable (receiver : A.M.Frame (Value := B.FC.Value initial) (Var := AT.Code.F.C.Var) (sort := ()))
local notation "cfg" => B.programme initial frame base before environment admissions observation nontrivial half sourceFrame
local notation "mat" => R.actualMaterial receiver cfg
local notation "maternal" => AT.Origin.sourceRaw initial frame base before environment admissions

def sourceEnd := linearEnd (mat).state
  ((B.material_raw initial frame base before environment admissions observation nontrivial half sourceFrame receiver).trans
    (AT.literal_shape observation nontrivial half initial maternal))
  (B.oldPaid initial frame base before environment admissions observation nontrivial half sourceFrame receiver)
  (WB.old_paid_const receiver cfg)

def read := C.read (Original.old receiver cfg) (Original.origin receiver cfg) (Original.reader receiver cfg)
  (sourceEnd observation nontrivial half initial frame base before environment admissions sourceFrame receiver).2.1
  (Original.source_state receiver cfg)
  (sourceEnd observation nontrivial half initial frame base before environment admissions sourceFrame receiver).2.2.1.down


/-- This is the original material, its returned primitive and its own canonical stage. -/
def sourceData :=
  let material := R.actualMaterial receiver cfg
  let ending := sourceEnd observation nontrivial half initial frame base before environment admissions sourceFrame receiver
  let stage := read observation nontrivial half initial frame base before environment admissions sourceFrame receiver
  PProd.mk material (PProd.mk ending stage)

section Indexed
variable (depth : Nat)
variable (carried : KC.H.Carrier (α := type_of% (KC.K.originalOutcome observation nontrivial half depth))
  (KC.K.originalOutcome observation nontrivial half depth) frame)
local notation "sf" => SP.born (V := AT.Code.F.BaseValue initial) frame base before environment admissions
local notation "current" => B.actualCurrent initial frame base before environment admissions observation nontrivial half sf
local notation "actualSource" => sourceData observation nontrivial half initial frame base before environment admissions sf current

private def IndexedResult :=
  Σ actual : KC.ResultAt observation nontrivial half depth initial frame base before environment admissions carried,
    PProd (actual = KC.readAt observation nontrivial half depth initial frame base before environment admissions carried)
      { source : type_of% actualSource // source = actualSource }

attribute [local irreducible] IndexedResult

private def consumeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
    (depth initial : Nat)
    (frame : A.M.Frame (Value := PairValue (AT.Code.F.BaseValue initial)) (Var := AT.Code.F.C.Var) (sort := ()))
    (base : A.Programme (PhysicalValue := PairValue (AT.Code.F.BaseValue initial)) (PhysicalVar := AT.Code.F.C.Var) (sort := ()))
    (before : Inventory (V := AT.Code.F.BaseValue initial) (X := AT.Code.F.C.Var) (s := ()))
    (environment : Env (AT.Code.F.BaseValue initial) AT.Code.F.C.Var)
    (admissions : List (AdmissionReceipt.Admission before (ActualNativeRelationTransport.AS.stockScalar frame base)))
    (carried : KC.H.Carrier (α := type_of% (KC.K.originalOutcome observation nontrivial half depth))
      (KC.K.originalOutcome observation nontrivial half depth) frame)
    (actual : KC.ResultAt observation nontrivial half depth initial frame base before environment admissions carried)
    (identity : actual = KC.readAt observation nontrivial half depth initial frame base before environment admissions carried) :
    IndexedResult observation nontrivial half initial frame base before environment admissions depth carried := by
  unfold IndexedResult
  let sourceFrame := SP.born (V := AT.Code.F.BaseValue initial) frame base before environment admissions
  let receiver := B.actualCurrent initial frame base before environment admissions observation nontrivial half sourceFrame
  let source := sourceData observation nontrivial half initial frame base before environment admissions sourceFrame receiver
  exact ⟨actual, identity, ⟨source,rfl⟩⟩
end Indexed

attribute [local irreducible] KC.ResultAt KC.readAt

local elab "sourceResult% " actualStx:term : term => do
  let actual ← Lean.Elab.Term.elabTerm actualStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let actual ← Lean.instantiateMVars actual
  let sourceType ← Lean.Meta.whnf (← Lean.Meta.inferType actual)
  unless sourceType.getAppFn.constName? == some ``KC.ResultAt do
    throwError "expected the existing KConsumer.ResultAt source type"
  let sourceArgs := sourceType.getAppArgs
  unless sourceArgs.size == 11 do
    throwError "unexpected KConsumer.ResultAt source arity: {sourceArgs.size}"
  let consumer ← Lean.Meta.mkConstWithFreshMVarLevels ``consumeAt
  let identity ← Lean.Meta.mkEqRefl actual
  return Lean.mkAppN consumer (sourceArgs ++ #[actual, identity])

variable (depth : Nat)
set_option backward.isDefEq.respectTransparency true in
private def FixedResultAt (ordinal : Nat) :=
  Σ' actual : type_of% (KC.originalRead observation nontrivial half depth ordinal),
    PProd (actual = KC.originalRead observation nontrivial half depth ordinal)
      (type_of% (sourceResult% (KC.originalRead observation nontrivial half depth ordinal).2))

attribute [local irreducible] FixedResultAt

set_option backward.isDefEq.respectTransparency true in
opaque originalRead (ordinal : Nat) : FixedResultAt observation nontrivial half depth ordinal := by
  unfold FixedResultAt
  let actual := KC.originalRead observation nontrivial half depth ordinal
  let consumed := sourceResult% actual.2
  exact ⟨actual,rfl,consumed⟩

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.RSourceStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
