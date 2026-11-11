import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.Born
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceInventoryExecutionFeed
open MeasureTheory NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Code
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action
 (binding sourceCode body_updated)
namespace CF
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.CF (codeAt code_base_value collapseValue)
end CF
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.F (BaseValue)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.F.C (Value Var)
end C
end F
namespace Operand
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.Operand (CodeValue bodyAt)
end Operand
namespace DR
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
 (sourceLiftOperator source_lift_operator_read sourceCollapseHom source_collapse_actual completeRSourceRead)
namespace L
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action.DR.L (Value groups)
end L
end DR
end Code
namespace Born
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born
 (code codeEnvironment material_environment actualTrace actualCurrent programme)
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Born.FC (Value)
end FC
end Born
namespace Two
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
 (actionCode unitShellCode shell_ast_value liftPairMap bothCorrection bothUnit bothTail bothInvisible negateBranches directions totalBranches
  sourceShift translatedCorrection translatedUnit translatedShell translatedInvisible fourTerms coefficient
  coordinate unitAction unit_action_signed_shell signedUnitResponse signedUnitSource signed_unit_realizes
  positive_source_radius_bound negative_source_radius_bound)
end Two
namespace Ret
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn (returnDirectionRead)
end Ret

namespace Shape
variable {W X : Unit → Type} [∀ t,AddCommGroup (W t)]
local instance groups (grade : Nat) : ∀ t,AddCommGroup (Code.DR.L.Value W grade t) := Code.DR.L.groups W grade

theorem code_linear (operation : PairValue W () →+ PairValue W ())
 (argument : Expr (PairValue W) X ()) (grade : Nat) :
 Code.CF.codeAt (.linear operation argument) grade =
 .linear (Code.DR.sourceLiftOperator operation grade) (Code.CF.codeAt argument grade) := by
 induction grade with
 | zero => rfl
 | succ grade previous =>
  change liftExpr (Code.CF.codeAt (.linear operation argument) grade)=_
  rw [previous]
  rfl

theorem code_add (left right : Expr (PairValue W) X ()) (grade : Nat) :
 Code.CF.codeAt (.add left right) grade =
 .add (Code.CF.codeAt left grade) (Code.CF.codeAt right grade) := by
 induction grade with
 | zero => rfl
 | succ grade previous =>
  change liftExpr (Code.CF.codeAt (.add left right) grade)=_
  rw [previous]
  rfl
end Shape

abbrev Branches := PairValue (PairValue Code.F.C.Value) ()
local instance baseGroups (n : Nat) : ∀ t,AddCommGroup (Code.F.BaseValue n t) := Code.DR.L.groups (PairValue Code.F.C.Value) n
local instance originGroups (n : Nat) : ∀ t,AddCommGroup (Code.DR.L.Value (Code.F.BaseValue n) 2 t) := Code.DR.L.groups (Code.F.BaseValue n) 2
local instance runtimeGroups (n : Nat) : ∀ t,AddCommGroup
 (Code.DR.L.Value (Code.DR.L.Value (Code.F.BaseValue n) 2) 0 t) := Code.DR.L.groups (Code.DR.L.Value (Code.F.BaseValue n) 2) 0
local instance codeGroups (n : Nat) : ∀ t,AddCommGroup (Code.Operand.CodeValue n t) := Code.DR.L.groups (Code.F.BaseValue n) 3
local instance valueGroups (n : Nat) : ∀ t,AddCommGroup (Born.FC.Value n t) := Code.DR.L.groups (Code.F.BaseValue n) 5
local instance valueAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (Born.FC.Value n t) :=
 (valueGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (n : Nat) (t : Unit) : AddZero (Born.FC.Value n t) := (valueAddZeroClass n t).toAddZero
local instance nextGroups (n : Nat) : ∀ t,AddCommGroup (PairValue (Born.FC.Value n) t) := Code.DR.L.groups (Code.F.BaseValue n) 6
local instance nextAddZeroClass (n : Nat) (t : Unit) : AddZeroClass (PairValue (Born.FC.Value n) t) :=
 (nextGroups n t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance nextAddZero (n : Nat) (t : Unit) : AddZero (PairValue (Born.FC.Value n) t) := (nextAddZeroClass n t).toAddZero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (Code.F.BaseValue initial))) (Var := Code.F.C.Var) (sort := ()))

abbrev Value := PairValue (Born.FC.Value initial)

def operation (action : Branches →+ Branches) : Value initial () →+ Value initial () :=
 pairLinear (Value := Born.FC.Value initial)
  (pairLinear (Value := PairValue (Code.Operand.CodeValue initial))
   (pairLinear (Value := Code.Operand.CodeValue initial)
    (Code.DR.sourceLiftOperator (W := Code.F.BaseValue initial)
     (Code.DR.sourceLiftOperator (W := PairValue Code.F.C.Value) action initial) 2)))

def compiled (expression : Expr (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var ()) :
 Expr (Value initial) Code.F.C.Var () :=
 liftExpr (liftExpr (liftExpr
  ((Code.CF.codeAt (Code.CF.codeAt expression initial) 2).subst (Code.binding initial raw))))

theorem compiled_linear (action : Branches →+ Branches)
 (expression : Expr (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var ()) :
 compiled initial raw (.linear action expression) =
 .linear (operation initial action) (compiled initial raw expression) := by
 simp only [compiled,Shape.code_linear,Expr.subst,liftExpr]
 rfl

theorem compiled_add (left right : Expr (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var ()) :
 compiled initial raw (.add left right) = .add (compiled initial raw left) (compiled initial raw right) := by
 simp only [compiled,Shape.code_add,Expr.subst,liftExpr]

abbrev body := compiled initial raw (.var (s:=()) ())
abbrev correction := operation initial (Two.liftPairMap (Two.bothCorrection observation nontrivial half)).toLinearMap.toAddMonoidHom
abbrev unit := operation initial (Two.liftPairMap (Two.bothUnit observation nontrivial half)).toLinearMap.toAddMonoidHom
abbrev tail := operation initial (Two.liftPairMap (Two.bothTail observation nontrivial half)).toLinearMap.toAddMonoidHom
abbrev negative := operation initial Two.negateBranches.toLinearMap.toAddMonoidHom
abbrev invisible := operation initial (Two.liftPairMap (Two.bothInvisible observation nontrivial half)).toLinearMap.toAddMonoidHom
abbrev returned := operation initial Ret.returnDirectionRead.toLinearMap.toAddMonoidHom

def literal : Expr (Value initial) Code.F.C.Var () :=
 .linear (returned initial)
  (.add (.add (.add
   (.linear (correction observation nontrivial half initial) (body initial raw))
   (.linear (unit observation nontrivial half initial) (body initial raw)))
   (.add (.linear (tail observation nontrivial half initial) (body initial raw))
    (.linear (negative initial) (.linear (unit observation nontrivial half initial) (body initial raw)))))
   (.linear (invisible observation nontrivial half initial) (body initial raw)))

theorem literal_shape : compiled initial raw (Code.sourceCode observation nontrivial half) =
 literal observation nontrivial half initial raw := by
 simp only [Code.sourceCode,Two.actionCode,Two.unitShellCode,compiled_linear,compiled_add]
 rfl

private def withShape {V X : Unit → Type} [∀ t,AddCommGroup (V t)]
 {environment : Env V X} {before after : Expr V X ()} {total : V ()}
 (same : before=after) (actual : Trace environment before (.const total)) : Trace environment after (.const total) :=
 Eq.mp (congrArg (fun expression => Trace environment expression (.const total)) same) actual

private def restore {V X : Unit → Type} [∀ t,AddCommGroup (V t)]
 {environment : Env V X} {before after expression : Expr V X ()} {total : V ()}
 (same : before=after) (actual : Trace environment before (.const total))
 (receipt : Trace.SourceReceipt (withShape same actual) expression) : Trace.SourceReceipt actual expression := by
 cases same
 exact receipt

variable (environment : Env (Value initial) Code.F.C.Var) (total : Value initial ())
variable (actual : Trace environment (compiled initial raw (Code.sourceCode observation nontrivial half)) (.const total))

def shaped := withShape (literal_shape observation nontrivial half initial raw) actual

def returnCut := (shaped observation nontrivial half initial raw environment total actual).splitLinear
def allCut := (returnCut observation nontrivial half initial raw environment total actual).trace.splitAdd
def shellCut := (allCut observation nontrivial half initial raw environment total actual).leftTrace.splitAdd
def pairCut := (shellCut observation nontrivial half initial raw environment total actual).leftTrace.splitAdd
def unitShellCut := (shellCut observation nontrivial half initial raw environment total actual).rightTrace.splitAdd

def correctionReceipt : Trace.SourceReceipt actual
 (.linear (correction observation nontrivial half initial) (body initial raw)) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 let p := pairCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨p.leftValue,p.leftTrace,.linear r (.left a (.left s (.left p (.refl _))))⟩

def unitReceipt : Trace.SourceReceipt actual
 (.linear (unit observation nontrivial half initial) (body initial raw)) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 let p := pairCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨p.rightValue,p.rightTrace,.linear r (.left a (.left s (.right p (.refl _))))⟩

def tailReceipt : Trace.SourceReceipt actual
 (.linear (tail observation nontrivial half initial) (body initial raw)) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 let u := unitShellCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨u.leftValue,u.leftTrace,.linear r (.left a (.right s (.left u (.refl _))))⟩

def negativeUnitReceipt : Trace.SourceReceipt actual
 (.linear (negative initial) (.linear (unit observation nontrivial half initial) (body initial raw))) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 let u := unitShellCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨u.rightValue,u.rightTrace,.linear r (.left a (.right s (.right u (.refl _))))⟩

def invisibleReceipt : Trace.SourceReceipt actual
 (.linear (invisible observation nontrivial half initial) (body initial raw)) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨a.rightValue,a.rightTrace,.linear r (.right a (.refl _))⟩

private theorem restore_address {V X : Unit → Type} [∀ t,AddCommGroup (V t)]
 {environment : Env V X} {before after expression : Expr V X ()} {total : V ()}
 (same : before=after) (actual : Trace environment before (.const total))
 (receipt : Trace.SourceReceipt (withShape same actual) expression) :
 (restore same actual receipt).retained.address=receipt.retained.address := by
 cases same
 rfl

def shellReceipt : Trace.SourceReceipt actual
 (.add (.linear (tail observation nontrivial half initial) (body initial raw))
  (.linear (negative initial) (.linear (unit observation nontrivial half initial) (body initial raw)))) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨s.rightValue,s.rightTrace,.linear r (.left a (.right s (.refl _)))⟩

def negativeOperandUnitReceipt : Trace.SourceReceipt actual
 (.linear (unit observation nontrivial half initial) (body initial raw)) :=
 let r := returnCut observation nontrivial half initial raw environment total actual
 let a := allCut observation nontrivial half initial raw environment total actual
 let s := shellCut observation nontrivial half initial raw environment total actual
 let u := unitShellCut observation nontrivial half initial raw environment total actual
 let n := u.rightTrace.splitLinear
 restore (literal_shape observation nontrivial half initial raw) actual
  ⟨n.input,n.trace,.linear r (.left a (.right s (.right u (.linear n (.refl _)))))⟩

theorem unit_address :
 (unitReceipt observation nontrivial half initial raw environment total actual).retained.address=[2,0,0,1] := by
 simp only [unitReceipt,restore_address,Trace.Subtrace.address]

theorem negative_operand_unit_address :
 (negativeOperandUnitReceipt observation nontrivial half initial raw environment total actual).retained.address=[2,0,1,1,2] := by
 simp only [negativeOperandUnitReceipt,restore_address,Trace.Subtrace.address]

theorem repeated_unit_positions :
 (unitReceipt observation nontrivial half initial raw environment total actual).retained.address ≠
 (negativeOperandUnitReceipt observation nontrivial half initial raw environment total actual).retained.address := by
 rw [unit_address,negative_operand_unit_address]
 decide

def inputReceipt : Trace.SourceReceipt actual (body initial raw) :=
 let c := correctionReceipt observation nontrivial half initial raw environment total actual
 let input := c.trace.splitLinear
 ⟨input.input,input.trace,c.retained.trans (.linear input (.refl _))⟩

def physicalRead (value : Value initial ()) : Branches :=
 Code.DR.completeRSourceRead initial 2 0 value.1.1.1

def oldEnvironmentThree : Env (Code.Operand.CodeValue initial) Code.F.C.Var :=
 fun target name => (environment target name).1.1.1

def inputEnvironment : Env (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var :=
 fun target name => by
  cases target
  exact Code.CF.collapseValue initial (Code.CF.collapseValue 2
   (((Code.binding initial raw) () name).eval (oldEnvironmentThree initial environment)))

private theorem eval_lift_first {V X : Unit → Type} [∀ t,AddCommGroup (V t)]
 (expression : Expr V X ()) (environment : Env (PairValue V) X) :
 ((liftExpr expression).eval environment).1 = expression.eval (fun target name => (environment target name).1) := by
 change ((liftExpr expression).eval (pairEnvironment
  (fun target name => (environment target name).1)
  (fun target name => (environment target name).2))).1 = _
 rw [eval_liftExpr]

private theorem compiled_old (expression : Expr (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var ()) :
 ((compiled initial raw expression).eval environment).1.1.1 =
 ((Code.CF.codeAt (Code.CF.codeAt expression initial) 2).subst (Code.binding initial raw)).eval
  (oldEnvironmentThree initial environment) := by
 simp only [compiled,eval_lift_first]
 rfl

theorem compiled_read (expression : Expr (PairValue (PairValue Code.F.C.Value)) Code.F.C.Var ()) :
 physicalRead initial ((compiled initial raw expression).eval environment) =
 expression.eval (inputEnvironment initial raw environment) := by
 unfold physicalRead
 rw [compiled_old]
 change Code.DR.sourceCollapseHom initial (Code.DR.sourceCollapseHom 2 _) = _
 rw [Code.DR.source_collapse_actual,Code.DR.source_collapse_actual,Expr.eval_subst,
  Code.CF.code_base_value,Code.CF.code_base_value]
 apply congrArg expression.eval
 funext target name
 cases target
 rfl

private def retarget {V X : Unit → Type} [∀ t,AddCommGroup (V t)]
 {environment : Env V X} {whole before after : Expr V X ()} {total : V ()}
 {actual : Trace environment whole (.const total)} (same : before=after)
 (receipt : Trace.SourceReceipt actual after) : Trace.SourceReceipt actual before := by
 cases same
 exact receipt

private theorem shell_shape : compiled initial raw (Two.unitShellCode observation nontrivial half) =
 .add (.linear (tail observation nontrivial half initial) (body initial raw))
  (.linear (negative initial) (.linear (unit observation nontrivial half initial) (body initial raw))) := by
 simp only [Two.unitShellCode,compiled_linear,compiled_add]

def actualShell : Trace.SourceReceipt actual (compiled initial raw (Two.unitShellCode observation nontrivial half)) :=
 retarget (shell_shape observation nontrivial half initial raw)
  (shellReceipt observation nontrivial half initial raw environment total actual)

theorem actual_shell_read :
 physicalRead initial (actualShell observation nontrivial half initial raw environment total actual).value =
 (Two.unitShellCode observation nontrivial half).eval (inputEnvironment initial raw environment) :=
 (congrArg (physicalRead initial)
  (completed_trace_value environment (actualShell observation nontrivial half initial raw environment total actual).trace)).trans
  (compiled_read initial raw environment (Two.unitShellCode observation nontrivial half))

theorem input_receipt_read :
 physicalRead initial (inputReceipt observation nontrivial half initial raw environment total actual).value =
 (inputEnvironment initial raw environment) () () :=
 (congrArg (physicalRead initial)
  (completed_trace_value environment (inputReceipt observation nontrivial half initial raw environment total actual).trace)).trans
  (compiled_read initial raw environment (.var (s:=()) ()))

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.ActualTrace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
