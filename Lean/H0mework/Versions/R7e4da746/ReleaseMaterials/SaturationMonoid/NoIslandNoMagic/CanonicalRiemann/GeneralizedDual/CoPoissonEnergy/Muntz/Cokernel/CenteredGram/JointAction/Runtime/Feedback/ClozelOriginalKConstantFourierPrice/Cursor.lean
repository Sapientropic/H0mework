import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Cursor.Linear
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKExteriorArithmeticCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceCursor
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace BF
export OriginalKBFiniteCalculation (Value Var E lossCode)
end BF
namespace PT
export SourceOperationPaidRelations (words complete_steps stepOccurrence stepOccurrence_word)
end PT
open private childAt decodeMap decodeFace from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource

namespace CursorRead
variable {environment:Env BF.Value BF.Var}
private theorem last_before {operation:BurnolL2→+BurnolL2} {body:BF.E} {total input:BurnolL2}
    {actual:Trace environment (.linear (s:=()) (t:=()) operation body) (.const total)} {inside:Trace environment body (.const input)}
    (interleaving:Trace.LinearInterleaving operation actual inside) :
    interleaving.lastCursor.beforeExpr=.linear (s:=()) (t:=()) operation (.const input) := by
  induction interleaving with
  | last => rfl
  | step paid tail previous => exact previous

private theorem left_before {left right:BF.E} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace) (cursor:Trace.Cursor leftTrace) :
    (interleaving.leftCursor cursor).beforeExpr=.add cursor.beforeExpr (interleaving.rightAtLeft cursor) := by
  induction interleaving with
  | last => cases cursor
  | left paid tail previous =>
    cases cursor with
    | here => rfl
    | there _ _ inside => exact previous inside
  | right paid tail previous => exact previous cursor

private theorem word_at {before after:BF.E} {actual:Trace environment before after} (cursor:Trace.Cursor actual) :
    (PT.words actual).get ⟨cursor.position,by rw [PT.complete_steps];exact cursor.position_lt⟩=
      relation (R:=ℤ) environment (.inl ⟨cursor.beforeExpr,cursor.afterExpr,cursor.paidStep.toDerivation⟩) := by
  induction cursor with
  | here => rfl
  | there paid tail inside previous => exact previous

theorem decode_before {before after:BF.E} (step:Step environment before after)
    (path:List Bool) (value:BurnolL2) (selected:childAt path before=.const value) :
    decodeMap (remaining before) path
      (relation (R:=ℤ) environment (.inl ⟨before,after,step.toDerivation⟩))=value := by
  have different : remaining after≠remaining before := by have decreases:=step.remaining_eq;omega
  simp [relation,decodeMap,decodeFace,different,selected,Expr.eval]
end CursorRead

variable (h:ℝ) (body:BF.E) (operation:BurnolL2→+BurnolL2)
variable {environment:Env BF.Value BF.Var} {total:BurnolL2}
variable (actual:Trace environment (.linear (s:=()) (t:=()) operation (BF.lossCode h body)) (.const total))

def outer := Trace.splitLinear actual
def loss := Trace.splitAdd (outer h body operation actual).trace
def exterior := Trace.splitAdd (loss h body operation actual).leftTrace
def dilation := Trace.splitLinear (exterior h body operation actual).leftTrace
def child : Trace.SourceReceipt actual body :=
  ⟨(dilation h body operation actual).input,(dilation h body operation actual).trace,
    .linear (outer h body operation actual) (.left (loss h body operation actual)
      (.left (exterior h body operation actual) (.linear (dilation h body operation actual) (.refl _))))⟩
def cursor : Trace.Cursor actual :=
  (outer h body operation actual).interleaving.liftCursor
    ((loss h body operation actual).interleaving.leftCursor
      ((exterior h body operation actual).interleaving.leftCursor
        (dilation h body operation actual).interleaving.lastCursor))

def path : List Bool := [false,false,false,false]
theorem cursor_stored : childAt path (cursor h body operation actual).beforeExpr=
    .const (child h body operation actual).value := by
  unfold cursor
  rw [Trace.LinearInterleaving.liftCursor_before,CursorRead.left_before,CursorRead.left_before,CursorRead.last_before]
  rfl

def index : Fin (PT.words actual).length :=
  ⟨(cursor h body operation actual).position,by rw [PT.complete_steps];exact (cursor h body operation actual).position_lt⟩
def occurrence := PT.stepOccurrence actual (index h body operation actual)
theorem occurrence_word : (occurrence h body operation actual).word=
    relation (R:=ℤ) environment (.inl ⟨(cursor h body operation actual).beforeExpr,
      (cursor h body operation actual).afterExpr,(cursor h body operation actual).paidStep.toDerivation⟩) :=
  CursorRead.word_at (cursor h body operation actual)

/-- The current word is read at an already executed constant child, so B is not evaluated again. -/
def storedValue : BurnolL2 := decodeMap (remaining (cursor h body operation actual).beforeExpr) path
  (occurrence h body operation actual).word
theorem stored_value : storedValue h body operation actual=(child h body operation actual).value := by
  unfold storedValue
  rw [occurrence_word]
  exact CursorRead.decode_before (cursor h body operation actual).paidStep path
    (child h body operation actual).value (cursor_stored h body operation actual)
theorem child_address : (child h body operation actual).retained.address=[2,0,0,2] := rfl

end OriginalConstantFourierPriceCursor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceCursor"
