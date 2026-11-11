import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Cursor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Current raw law action targetOf nextState runtimeCurrent)
export RootGeneratedDebtActivationJointSource.OwnerFree (tick_math)
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (frontier target_state)
end Calc
namespace Consumer
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (trace targetState)
end Consumer
end OF

namespace Canonical
universe u
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := sort))
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion
  (state next_state budget history_accounting completed_history_length)
end C

private structure Extension (first second : OF.Current old origin reader) where
  rest : Trace (OF.raw old origin reader).environment first.1 second.1
  reconstruct : first.2.append rest = second.2

private def Extension.trans {first second third : OF.Current old origin reader}
    (left : Extension old origin reader first second)
    (right : Extension old origin reader second third) : Extension old origin reader first third :=
  ⟨left.rest.append right.rest, by
    rw [← Trace.append_assoc, left.reconstruct, right.reconstruct]⟩

private def extensionStep (state : OF.Current old origin reader) :
    Extension old origin reader state (OF.nextState old origin reader state) := by
  unfold OF.nextState OF.targetOf
  cases selected : OF.action old origin reader state with
  | inl settled => exact ⟨.nil _, Trace.append_nil _⟩
  | inr generated =>
      rcases generated with ⟨next, advance⟩
      cases advance with
      | paid step => exact ⟨.single step, rfl⟩

private def extension (start : Nat) : (count : Nat) →
    Extension old origin reader (C.state old origin reader start) (C.state old origin reader (start + count))
  | 0 => ⟨.nil _, Trace.append_nil _⟩
  | count + 1 =>
      let previous := Extension.trans old origin reader (extension start count)
        (extensionStep old origin reader (C.state old origin reader (start + count)))
      Eq.mp (congrArg (Extension old origin reader (C.state old origin reader start))
        (C.next_state old origin reader (start + count)).symm) previous

def active (index : Fin (remaining (OF.raw old origin reader).expression)) :
    Σ terminal : Expr Value Var sort,
      Σ paid : Step (OF.raw old origin reader).environment (C.state old origin reader index.1).1 terminal,
        PLift (OF.action old origin reader (C.state old origin reader index.1) =
          .inr ⟨SourceOperationExecutionDebt.advance (C.state old origin reader index.1) paid,
            SourceOperationExecutionDebt.Advance.paid paid⟩) := by
  cases selected : OF.action old origin reader (C.state old origin reader index.1) with
  | inl settled =>
      have zero := (OF.law old origin reader).settlement_budget_zero settled
      have budget := C.budget old origin reader index.1
      change remaining (C.state old origin reader index.1).1 = 0 at zero
      have bound := index.2
      omega
  | inr generated =>
      rcases generated with ⟨next, advance⟩
      cases advance with
      | paid step => exact ⟨_, step, ⟨rfl⟩⟩

private theorem active_next (index : Fin (remaining (OF.raw old origin reader).expression)) :
    C.state old origin reader (index.1+1) =
      SourceOperationExecutionDebt.advance (C.state old origin reader index.1) (active old origin reader index).2.1 := by
  exact (C.next_state old origin reader index.1).trans
    (congrArg (OF.targetOf old origin reader (C.state old origin reader index.1))
      (active old origin reader index).2.2.down)

theorem trace_heq {first second : OF.Current old origin reader} (same : first = second) :
    HEq first.2 second.2 := by cases same; rfl

/-- The cursor is read back from the source's own accumulated paid history. -/
def cursor (index : Fin (remaining (OF.raw old origin reader).expression)) :
    Σ cursor : Trace.Cursor (C.state old origin reader (remaining (OF.raw old origin reader).expression)).2,
      PLift (cursor.position = index.1) ×
      PLift (HEq cursor.paidStep (active old origin reader index).2.1) := by
  let selected := active old origin reader index
  let atNext := Trace.Cursor.transfer (active_next old origin reader index).symm
    (Trace.Cursor.last (C.state old origin reader index.1).2 selected.2.1)
  have endpoint : index.1+1 + (remaining (OF.raw old origin reader).expression - (index.1+1)) =
      remaining (OF.raw old origin reader).expression := by have bound := index.2; omega
  let toEnd : Extension old origin reader (C.state old origin reader (index.1+1))
      (C.state old origin reader (remaining (OF.raw old origin reader).expression)) :=
    Eq.mp (congrArg (fun count => Extension old origin reader (C.state old origin reader (index.1+1))
      (C.state old origin reader count)) endpoint)
      (extension old origin reader (index.1+1) (remaining (OF.raw old origin reader).expression - (index.1+1)))
  have joined : (⟨(C.state old origin reader (remaining (OF.raw old origin reader).expression)).1,
      (C.state old origin reader (index.1+1)).2.append toEnd.rest⟩ : OF.Current old origin reader) =
      C.state old origin reader (remaining (OF.raw old origin reader).expression) :=
    congrArg (fun history => (⟨(C.state old origin reader (remaining (OF.raw old origin reader).expression)).1,
      history⟩ : OF.Current old origin reader)) toEnd.reconstruct
  let atEnd := Trace.Cursor.transfer joined (atNext.extend toEnd.rest)
  refine ⟨atEnd, ⟨?_⟩, ⟨?_⟩⟩
  · have atNextPosition := Trace.Cursor.transfer_position (active_next old origin reader index).symm
      (Trace.Cursor.last (C.state old origin reader index.1).2 selected.2.1)
    have atEndPosition := Trace.Cursor.transfer_position joined (atNext.extend toEnd.rest)
    have pastLength : (C.state old origin reader index.1).2.length = index.1 := by
      have account := C.history_accounting old origin reader index.1
      have budget := C.budget old origin reader index.1
      have bound := index.2
      omega
    exact atEndPosition.trans ((Trace.Cursor.extend_position atNext toEnd.rest).trans
      (atNextPosition.trans ((Trace.Cursor.last_position (actual := (C.state old origin reader index.1).2) selected.2.1).trans pastLength)))
  · exact (Trace.Cursor.transfer_step joined (atNext.extend toEnd.rest)).trans
      ((Trace.Cursor.extend_step atNext toEnd.rest).trans
        ((Trace.Cursor.transfer_step (active_next old origin reader index).symm
          (Trace.Cursor.last (C.state old origin reader index.1).2 selected.2.1)).trans
            (Trace.Cursor.last_step (actual := (C.state old origin reader index.1).2) selected.2.1)))

def stageAt (index : Fin (remaining (OF.raw old origin reader).expression)) :=
  (OF.Calc.frontier old origin reader).history.stageAt
    ⟨index.1, Nat.lt_trans index.2 (Nat.lt_succ_self _)⟩

def paidIndex {terminal : Expr Value Var sort}
    {actual : Trace (OF.raw old origin reader).environment (OF.raw old origin reader).expression terminal}
    (sourceCursor : Trace.Cursor actual)
    (same : (⟨terminal, actual⟩ : OF.Current old origin reader) = OF.Consumer.targetState old origin reader) :
    Fin (remaining (OF.raw old origin reader).expression) :=
  let history := Trace.Cursor.transfer (same.trans (OF.Calc.target_state old origin reader)) sourceCursor
  ⟨history.position, lt_of_lt_of_eq (Trace.Cursor.position_lt _)
    (C.completed_history_length old origin reader)⟩

structure ReadAt {terminal : Expr Value Var sort}
    {actual : Trace (OF.raw old origin reader).environment (OF.raw old origin reader).expression terminal}
    (sourceCursor : Trace.Cursor actual)
    (same : (⟨terminal, actual⟩ : OF.Current old origin reader) = OF.Consumer.targetState old origin reader)
    {Physical : Type u} (physical : Physical) : Prop where
  identity : (cursor old origin reader (paidIndex old origin reader sourceCursor same)).1 =
    Trace.Cursor.transfer (same.trans (OF.Calc.target_state old origin reader)) sourceCursor
  sourceStep : HEq (active old origin reader (paidIndex old origin reader sourceCursor same)).2.1 sourceCursor.paidStep
  actualStep : HEq (active old origin reader (paidIndex old origin reader sourceCursor same)).2.1 physical
  nextMath : OF.runtimeCurrent old origin reader
      (stageAt old origin reader (paidIndex old origin reader sourceCursor same)).next =
    SourceOperationExecutionDebt.advance
      (C.state old origin reader (paidIndex old origin reader sourceCursor same).1)
      (active old origin reader (paidIndex old origin reader sourceCursor same)).2.1
  factorizes : type_of%
    (stageAt old origin reader (paidIndex old origin reader sourceCursor same)).factorizes

def read {terminal : Expr Value Var sort}
    {actual : Trace (OF.raw old origin reader).environment (OF.raw old origin reader).expression terminal}
    (sourceCursor : Trace.Cursor actual)
    (same : (⟨terminal, actual⟩ : OF.Current old origin reader) = OF.Consumer.targetState old origin reader)
    {Physical : Type u} {physical : Physical}
    (physicalSource : HEq sourceCursor.paidStep physical) :
    PProd (Trace.Cursor actual × Fin (remaining (OF.raw old origin reader).expression))
      (ReadAt old origin reader sourceCursor same physical) :=
  let history := Trace.Cursor.transfer (same.trans (OF.Calc.target_state old origin reader)) sourceCursor
  let index := paidIndex old origin reader sourceCursor same
  let owned := cursor old origin reader index
  let selected := active old origin reader index
  let stage := stageAt old origin reader index
  have identity : owned.1 = history :=
    Trace.Cursor.eq_of_position _ _ owned.2.1.down
  have original : HEq owned.1.paidStep sourceCursor.paidStep :=
    (show HEq owned.1.paidStep history.paidStep by rw [identity]; rfl).trans
      (Trace.Cursor.transfer_step _ _)
  have sourceStep := owned.2.2.down.symm.trans original
  have nextMath : OF.runtimeCurrent old origin reader stage.next =
      SourceOperationExecutionDebt.advance (C.state old origin reader index.1) selected.2.1 :=
    (OF.tick_math old origin reader _).trans
      (congrArg (OF.targetOf old origin reader (C.state old origin reader index.1)) selected.2.2.down)
  PProd.mk (sourceCursor, index)
    ⟨identity, sourceStep, sourceStep.trans physicalSource, nextMath, stage.factorizes⟩

end Canonical

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
