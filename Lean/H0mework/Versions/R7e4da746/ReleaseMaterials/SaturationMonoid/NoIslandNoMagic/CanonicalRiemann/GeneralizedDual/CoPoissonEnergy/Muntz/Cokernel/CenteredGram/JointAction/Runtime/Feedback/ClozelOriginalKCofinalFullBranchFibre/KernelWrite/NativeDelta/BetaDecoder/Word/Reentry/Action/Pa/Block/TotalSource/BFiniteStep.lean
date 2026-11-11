import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Responsibility.Debt.Activation.Root.Direct.JointSource.OwnerFree.CanonicalTrace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion BurnolPhysicalState
namespace BF
export OriginalKBFiniteCalculation (Base reader result code coordinate fixedShift)
end BF
namespace Canonical
universe u
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := sort))
private theorem result_state
    (readerFamily : {current : V.Current} →
      old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
        RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := sort))
    (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old readerFamily occurrence).2.1 =
      OF.Consumer.targetState old origin (fun _ => readerFamily occurrence) := rfl

end Canonical

namespace StepShape
universe u v w
variable {S : Type u} {V : S → Type v} {X : S → Type w}
  [∀ target, AddCommGroup (V target)] {environment : Env V X} {s : S}
private abbrev Data := Σ before : Expr V X s, Σ after : Expr V X s, Step environment before after

private def data {before after : Expr V X s} {actual : Trace environment before after}
    (cursor : Trace.Cursor actual) : Data (environment := environment) (s := s) :=
  ⟨cursor.beforeExpr,cursor.afterExpr,cursor.paidStep⟩

private theorem paid_heq {first second : Data (environment := environment) (s := s)} (same : first = second) :
    HEq first.2.2 second.2.2 := by cases same; rfl

private theorem linear {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : Trace.LinearInterleaving operation actual inside) :
    data interleaving.lastCursor = ⟨.linear operation (.const input),.const (operation input),.linearConst operation input⟩ := by
  induction interleaving with
  | last => rfl
  | step paid tail previous => exact previous

private theorem left {left right : Expr V X s} {total leftValue rightValue : V s}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : Trace.AddInterleaving environment actual leftTrace rightTrace)
    (cursor : Trace.Cursor leftTrace) :
    data (interleaving.leftCursor cursor) =
      ⟨.add cursor.beforeExpr (interleaving.rightAtLeft cursor),
        .add cursor.afterExpr (interleaving.rightAtLeft cursor),
        .addLeft cursor.paidStep⟩ := by
  induction interleaving with
  | last => cases cursor
  | left paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inside => exact previous inside
  | right paid tail previous => exact previous cursor

theorem leftLinearLast {operation : V s →+ V s} {body right : Expr V X s} {total leftValue rightValue input : V s}
    {actual : Trace environment (.add (.linear operation body) right) (.const total)}
    {leftTrace : Trace environment (.linear operation body) (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    {inside : Trace environment body (.const input)}
    (outer : Trace.AddInterleaving environment actual leftTrace rightTrace)
    (inner : Trace.LinearInterleaving operation leftTrace inside) :
    HEq (outer.leftCursor inner.lastCursor).paidStep
      (Step.addLeft (right := outer.rightAtLeft inner.lastCursor) (Step.linearConst (environment := environment) operation input)) := by
  have lifted := congrArg (fun item : Data (environment := environment) (s := s) =>
    (⟨.add item.1 (outer.rightAtLeft inner.lastCursor),
      .add item.2.1 (outer.rightAtLeft inner.lastCursor),
      .addLeft item.2.2⟩ : Data (environment := environment) (s := s))) (linear inner)
  exact paid_heq ((left outer inner.lastCursor).trans lifted)
end StepShape

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable {current : CanonicalUnitArithmeticRoot.V.Current}
variable (occurrence : BF.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)

def materialStage (index : Fin (remaining (BF.reader observation nontrivial half occurrence).expression + 1)) :=
  (OF.Calc.frontier BF.Base current (fun _ => BF.reader observation nontrivial half occurrence)).history.stageAt index

theorem stage_factorizes (index : Fin (remaining (BF.reader observation nontrivial half occurrence).expression + 1)) :
    type_of% (materialStage observation nontrivial half occurrence index).factorizes :=
  (materialStage observation nontrivial half occurrence index).factorizes

def rCursor : Trace.Cursor
    (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence) :=
  let cut := Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)
  let input := Trace.splitLinear cut.leftTrace
  cut.interleaving.leftCursor input.interleaving.lastCursor

theorem r_step : type_of% (show HEq (rCursor observation nontrivial half occurrence).paidStep _ from
    StepShape.leftLinearLast
      (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).interleaving
      (Trace.splitLinear (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).leftTrace).interleaving) :=
  show HEq (rCursor observation nontrivial half occurrence).paidStep _ from StepShape.leftLinearLast
      (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).interleaving
      (Trace.splitLinear (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).leftTrace).interleaving

theorem r_position : type_of% (Trace.AddInterleaving.leftCursor_position
      (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).interleaving
      (Trace.splitLinear (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).leftTrace).interleaving.lastCursor) :=
  Trace.AddInterleaving.leftCursor_position
      (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).interleaving
      (Trace.splitLinear (Trace.splitAdd (OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence)).leftTrace).interleaving.lastCursor

private theorem source_material_state :
    (⟨.const (BF.result observation nontrivial half occurrence).2.2.1,
      OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence⟩ :
      SourceOperationExecutionDebt.State OriginalKBFiniteCalculation.sourceEnvironment
        (BF.code (BF.coordinate observation nontrivial half occurrence) BF.fixedShift)) =
      (BF.result observation nontrivial half occurrence).2.1 := by
  refine Eq.trans ?_ (Sigma.eta (BF.result observation nontrivial half occurrence).2.1)
  unfold OriginalTotalSourceBFiniteAction.Source.actualTrace
  extract_lets endpoint
  exact Trace.Cursor.endpoint_state _ endpoint

theorem source_state :
    (⟨.const (BF.result observation nontrivial half occurrence).2.2.1,
      OriginalTotalSourceBFiniteAction.Source.actualTrace observation nontrivial half occurrence⟩ :
      SourceOperationExecutionDebt.State OriginalKBFiniteCalculation.sourceEnvironment
        (BF.code (BF.coordinate observation nontrivial half occurrence) BF.fixedShift)) =
      OF.Consumer.targetState BF.Base current (fun _ => BF.reader observation nontrivial half occurrence) :=
  let exactState : (BF.result observation nontrivial half occurrence).2.1 =
      OF.Consumer.targetState BF.Base current (fun _ => BF.reader observation nontrivial half occurrence) :=
    Canonical.result_state BF.Base current (BF.reader observation nontrivial half) occurrence
  (source_material_state observation nontrivial half occurrence).trans exactState

/-- The original parent step supplies this exact old calculation stage and its next. -/
def read :=
  Canonical.read (Value := OriginalKBFiniteCalculation.Value)
    (Var := OriginalKBFiniteCalculation.Var) BF.Base current
    (fun _ => BF.reader observation nontrivial half occurrence)
    (rCursor observation nontrivial half occurrence) (source_state observation nontrivial half occurrence)
    (r_step observation nontrivial half occurrence)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
