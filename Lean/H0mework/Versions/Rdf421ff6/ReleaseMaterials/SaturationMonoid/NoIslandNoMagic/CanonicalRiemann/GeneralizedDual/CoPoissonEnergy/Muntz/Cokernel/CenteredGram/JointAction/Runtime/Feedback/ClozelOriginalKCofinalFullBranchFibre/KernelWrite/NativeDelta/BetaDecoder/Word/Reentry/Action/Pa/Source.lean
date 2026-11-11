import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Programme
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResidualRNativeSuccessor.Projection

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
 (BaseValue sourceRaw sourceEnvironment pairEnvironmentAt prefixResultFace source sourceLaw sourceAt programme fullWrite born)
end F
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResidualRNativeSuccessor
 (sourcePaLift sourceNonPaLift source_lift_split_sum source_Pa_lift_read source_nonPa_lift_read sourcePaInput sourceNonPaInput source_Pa_qualified)
end P

abbrev CodeValue (initial : Nat) := PairValue (PairValue (PairValue (BaseValue initial)))
local instance baseGroups (initial : Nat) : ∀ target,AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ target,AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ target,AddCommGroup
 (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 target) :=
 DR.L.groups (DR.L.Value (BaseValue initial) 2) 0

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))

def bodyAt : Expr (CodeValue initial) C.Var () :=
 .linear (s:=()) (t:=()) (DR.completeResidualTotalRole initial 2 0) (liftExpr raw.expression)

def paBodyAt : Expr (CodeValue initial) C.Var () :=
 .linear (s:=()) (t:=()) (P.sourcePaLift initial 2 0) (bodyAt initial raw)

def nonPaBodyAt : Expr (CodeValue initial) C.Var () :=
 .linear (s:=()) (t:=()) (P.sourceNonPaLift initial 2 0) (bodyAt initial raw)

def paActionAt : Expr (CodeValue initial) C.Var () :=
 .linear (s:=()) (t:=()) (DR.completeRSourceAction observation nontrivial half initial 2 0) (paBodyAt initial raw)

def nonPaActionAt : Expr (CodeValue initial) C.Var () :=
 .linear (s:=()) (t:=()) (DR.completeRSourceAction observation nontrivial half initial 2 0) (nonPaBodyAt initial raw)

def codeAt : Expr (CodeValue initial) C.Var () :=
 .add (paActionAt observation nontrivial half initial raw) (nonPaActionAt observation nontrivial half initial raw)

theorem code_at_read (environment : Env (CodeValue initial) C.Var) :
 (codeAt observation nontrivial half initial raw).eval environment =
 DR.completeRSourceAction observation nontrivial half initial 2 0 ((bodyAt initial raw).eval environment) := by
 change DR.completeRSourceAction observation nontrivial half initial 2 0
  (P.sourcePaLift initial 2 0 ((bodyAt initial raw).eval environment))+
  DR.completeRSourceAction observation nontrivial half initial 2 0
   (P.sourceNonPaLift initial 2 0 ((bodyAt initial raw).eval environment)) = _
 rw [← map_add, P.source_lift_split_sum]

variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))
variable {current : J.Current sourceFrame.registered}
variable (supplied : I.Occurrence sourceFrame (current := current))

abbrev body := bodyAt initial (F.sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)
abbrev paBody := paBodyAt initial (F.sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)
abbrev nonPaBody := nonPaBodyAt initial (F.sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)
abbrev code := codeAt observation nontrivial half initial
 (F.sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)

def codeReader : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := CodeValue initial) (Var := C.Var) (sort := ()) :=
 ⟨F.pairEnvironmentAt initial frame base before oldEnvironment admissions sourceFrame supplied,
  code observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied⟩

theorem code_reader_uniform {otherCurrent : J.Current sourceFrame.registered}
 (other : I.Occurrence sourceFrame (current := otherCurrent)) :
 codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied =
 codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame other := rfl

variable (environment updatedEnvironment : Env (CodeValue initial) C.Var)
variable (oldValue nativeValue : CodeValue initial ())
variable (oldTrace : Trace environment (codeAt observation nontrivial half initial raw) (.const oldValue))
variable (nativeTrace : Trace updatedEnvironment
 (.add (codeAt observation nontrivial half initial raw)
  (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) (.const oldValue))) (.const nativeValue))

/-- Both updated legs are nested subtraces of this actual native residual history. -/
structure SplitAt where
 old : Trace.AddSplit oldTrace
 native : Trace.AddSplit nativeTrace
 updated : Trace.AddSplit native.leftTrace

def splitAt : SplitAt observation nontrivial half initial raw environment updatedEnvironment oldValue nativeValue oldTrace nativeTrace :=
 let old := oldTrace.splitAdd
 let native := nativeTrace.splitAdd
 ⟨old,native,native.leftTrace.splitAdd⟩

namespace SplitAt
variable (result : SplitAt observation nontrivial half initial raw environment updatedEnvironment oldValue nativeValue oldTrace nativeTrace)

def fullInput (_result : SplitAt observation nontrivial half initial raw environment updatedEnvironment oldValue nativeValue oldTrace nativeTrace) : CodeValue initial () :=
 (bodyAt initial raw).eval updatedEnvironment

def oldPa : CodeValue initial () := result.old.leftValue
def oldNonPa : CodeValue initial () := result.old.rightValue
def updatedPa : CodeValue initial () := result.updated.leftValue
def updatedNonPa : CodeValue initial () := result.updated.rightValue
def paEffect : CodeValue initial () := result.updatedPa-result.oldPa
def nonPaEffect : CodeValue initial () := result.updatedNonPa-result.oldNonPa

theorem old_sum : oldValue=result.oldPa+result.oldNonPa := result.old.total_eq

theorem right_old : result.native.rightValue = -oldValue :=
 completed_trace_value updatedEnvironment result.native.rightTrace

theorem raw_updated : result.native.leftValue=oldValue+nativeValue := by
 have total := result.native.total_eq
 rw [result.right_old] at total
 calc
  result.native.leftValue = (result.native.leftValue + -oldValue)+oldValue := by abel
  _ = nativeValue+oldValue := congrArg (fun value => value+oldValue) total.symm
  _ = oldValue+nativeValue := add_comm _ _

theorem updated_sum : oldValue+nativeValue=result.updatedPa+result.updatedNonPa :=
 result.raw_updated.symm.trans result.updated.total_eq

theorem effect_sum : nativeValue=result.paEffect+result.nonPaEffect := by
 have old := result.old_sum
 have updated := result.updated_sum
 calc
  nativeValue = (oldValue+nativeValue)-oldValue := by abel
  _ = (result.updatedPa+result.updatedNonPa)-(result.oldPa+result.oldNonPa) :=
   congrArg₂ (· - ·) updated old
  _ = result.paEffect+result.nonPaEffect := by dsimp only [paEffect,nonPaEffect]; abel

theorem pa_action : result.updatedPa =
 DR.completeRSourceAction observation nontrivial half initial 2 0
  (P.sourcePaLift initial 2 0 (result.fullInput)) :=
 completed_trace_value updatedEnvironment result.updated.leftTrace

theorem nonPa_action : result.updatedNonPa =
 DR.completeRSourceAction observation nontrivial half initial 2 0
  (P.sourceNonPaLift initial 2 0 (result.fullInput)) :=
 completed_trace_value updatedEnvironment result.updated.rightTrace

theorem pa_read : DR.completeRSourceRead initial 2 0 result.updatedPa =
 RPhysical.variableAction observation nontrivial half
  (P.sourcePaInput (DR.completeRSourceRead initial 2 0 result.fullInput)) := by
 rw [result.pa_action,DR.complete_R_source_action_read,P.source_Pa_lift_read]

theorem nonPa_read : DR.completeRSourceRead initial 2 0 result.updatedNonPa =
 RPhysical.variableAction observation nontrivial half
  (P.sourceNonPaInput (DR.completeRSourceRead initial 2 0 result.fullInput)) := by
 rw [result.nonPa_action,DR.complete_R_source_action_read,P.source_nonPa_lift_read]

theorem pa_effect_source : result.paEffect =
 (paActionAt observation nontrivial half initial raw).effect environment (updatedEnvironment-environment) := by
 have actual := Expr.eval_update (paActionAt observation nontrivial half initial raw) environment (updatedEnvironment-environment)
 rw [add_sub_cancel] at actual
 have old := completed_trace_value environment result.old.leftTrace
 have updated := completed_trace_value updatedEnvironment result.updated.leftTrace
 change result.updated.leftValue-result.old.leftValue = _
 calc
  result.updated.leftValue-result.old.leftValue =
   (paActionAt observation nontrivial half initial raw).eval updatedEnvironment-
    (paActionAt observation nontrivial half initial raw).eval environment := congrArg₂ (· - ·) updated old
  _ = _ := by rw [actual]; abel

theorem nonPa_effect_source : result.nonPaEffect =
 (nonPaActionAt observation nontrivial half initial raw).effect environment (updatedEnvironment-environment) := by
 have actual := Expr.eval_update (nonPaActionAt observation nontrivial half initial raw) environment (updatedEnvironment-environment)
 rw [add_sub_cancel] at actual
 have old := completed_trace_value environment result.old.rightTrace
 have updated := completed_trace_value updatedEnvironment result.updated.rightTrace
 change result.updated.rightValue-result.old.rightValue = _
 calc
  result.updated.rightValue-result.old.rightValue =
   (nonPaActionAt observation nontrivial half initial raw).eval updatedEnvironment-
    (nonPaActionAt observation nontrivial half initial raw).eval environment := congrArg₂ (· - ·) updated old
  _ = _ := by rw [actual]; abel

theorem updated_full : oldValue+nativeValue =
 DR.completeRSourceAction observation nontrivial half initial 2 0 result.fullInput := by
 calc
  oldValue+nativeValue = result.updatedPa+result.updatedNonPa := result.updated_sum
  _ = DR.completeRSourceAction observation nontrivial half initial 2 0
    (P.sourcePaLift initial 2 0 result.fullInput)+
   DR.completeRSourceAction observation nontrivial half initial 2 0
    (P.sourceNonPaLift initial 2 0 result.fullInput) := congrArg₂ (· + ·) result.pa_action result.nonPa_action
  _ = _ := by rw [← map_add,P.source_lift_split_sum]

theorem native_length : nativeTrace.length =
 result.updated.leftTrace.length+result.updated.rightTrace.length+result.native.rightTrace.length+2 := by
 have top := result.native.length_eq
 have raw := result.updated.length_eq
 omega

end SplitAt
end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
