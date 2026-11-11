import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base root actualOccurrence)
end Q
namespace OI
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultLaw)
end OI
namespace Mat
export SourceGeneratedInquiryReceiptAction.Configured.Material
 (programme initial generatedAction runtime runtime_initial target_next compiles whole_first successor_valid
  nextMaterialFace material oldPaid receipt selected nativeValue born old_paid_const selected_raw updated_total
  native_effect native_inverse actual_writeback actual_receipt_next actual_receipt_compiles)
end Mat
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme)
end WB
namespace R
export SourceGeneratedInquiryReceiptAction (occurrence actualMaterial actionResultAt afterEnvironment)
end R

local instance programmeBaseGroups (initial : Nat) : ∀ target,AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance programmeOriginGroups (initial : Nat) : ∀ target,AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance programmeRuntimeGroups (initial : Nat) : ∀ target,AddCommGroup
 (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 target) :=
 DR.L.groups (DR.L.Value (BaseValue initial) 2) 0
variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))

def receiptLaw := OI.resultLaw (Q.base sourceFrame).root.toAuthoritativeRoot
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def fullSource := (Q.root sourceFrame
 (F.programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base.withProjectionCoface
 (receiptLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def programme : A.Programme (PhysicalValue := PairValue (PairValue (BaseValue initial))) (PhysicalVar := C.Var) (sort := ()) :=
 { F.programme observation nontrivial half initial frame base before oldEnvironment admissions with
   datum := fun sourceFrame => {
    (F.programme observation nontrivial half initial frame base before oldEnvironment admissions).datum sourceFrame with
    component := some (fullSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).projectionLaw
    calculationReader := some (fun {_current} supplied =>
     codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied) } }

def oldLawInComponent := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (Q.root sourceFrame (F.programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base
 (receiptLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

abbrev lowBase := WB.programme sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions) (F.fullWrite initial)
abbrev generatedAction := Mat.generatedAction sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev runtime := Mat.runtime sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev nextSplitFace := Mat.nextMaterialFace sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
def material : RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value := CodeValue initial) (Var := C.Var) (sort := ())
 (lower := (SourceGeneratedInquiryReceiptAction.old sourceFrame
  (programme observation nontrivial half initial frame base before oldEnvironment admissions)).root.toAuthoritativeRoot.toLedgerRoot)
 (current := SourceGeneratedInquiryReceiptAction.current sourceFrame
  (programme observation nontrivial half initial frame base before oldEnvironment admissions))
 (R.occurrence sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)) :=
 (nextSplitFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead.prefixMaterial
def oldPaid : CodeValue initial () := (nextSplitFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead.prefixResult.2.2.1
abbrev receipt := Mat.receipt sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev selected := Mat.selected sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
def nativeValue : CodeValue initial () := Mat.nativeValue sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev nativeBorn := Mat.born sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

private def closeTrace {environment : Env (CodeValue initial) C.Var}
 {expression : Expr (CodeValue initial) C.Var ()}
 (state : SourceOperationExecutionDebt.State environment expression) (value : CodeValue initial ())
 (paid : state.1=.const value) : Trace environment expression (.const value) :=
 Eq.mp (congrArg (fun terminal => Trace environment expression terminal) paid) state.2

def inputRaw := F.sourceRaw initial frame base before oldEnvironment admissions (A.epoch sourceFrame)
 (R.occurrence sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions))

theorem material_raw : (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).raw =
 codeAt observation nontrivial half initial
  (inputRaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := rfl

theorem old_paid_const :
 (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).state.1 =
 .const (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 Mat.old_paid_const sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

theorem native_terminal :
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state.1 =
 .const (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (receipt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).2.1.2.down

theorem initial_raw :
 (Mat.initial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).rawRead =
 (⟨(material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment+
   (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).increment,
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
   (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)⟩ :
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := CodeValue initial) (Var := C.Var) (sort := ())) := rfl

section NativeTransport
attribute [local irreducible] material oldPaid nativeValue

def oldTrace : Trace
 (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment
 (codeAt observation nontrivial half initial (inputRaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 (.const (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 Eq.mp (congrArg (fun expression : Expr (CodeValue initial) C.Var () =>
   Trace (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment
    expression (.const (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)))
  (material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 (closeTrace initial (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).state
  (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  (old_paid_const observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))

def nativeTrace : Trace
 ((material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment+
  (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).increment)
 (.add (codeAt observation nontrivial half initial (inputRaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
  (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) (.const (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))))
 (.const (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := by
 let actual := closeTrace initial
  (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state
  (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  (native_terminal observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 have sameRaw := Mat.selected_raw sourceFrame
  (programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 have sourceRaw := sameRaw.trans (initial_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 let moved := Eq.mp (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := CodeValue initial) (Var := C.Var) (sort := ()) =>
    Trace raw.environment raw.expression (.const (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))) sourceRaw) actual
 have terminal := old_paid_const observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
 change Trace _ (.add (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).raw
  (.linear (-AddMonoidHom.id _) (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).state.1)) _ at moved
 have expressionEq := congrArg₂ (fun (raw terminal : Expr (CodeValue initial) C.Var ()) =>
  Expr.add raw (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) terminal))
  (material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) terminal
 exact Eq.mp (congrArg (fun expression : Expr (CodeValue initial) C.Var () =>
  Trace ((material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment+
    (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).increment)
   expression (.const (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))) expressionEq) moved

def nextSplitAt := splitAt observation nontrivial half initial
 (inputRaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment
 ((material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).environment+
  (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).increment)
 (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (oldTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (nativeTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

end NativeTransport

attribute [local irreducible] nextSplitAt

private def nativeUpdatedRAt : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 ((nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).activeEnvironment () ())

def nativeUpdatedR : PairValue (PairValue C.Value) () :=
 nativeUpdatedRAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def nextInput : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).fullInput

def nextPaR : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedPa

def nextNonPaR : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedNonPa

attribute [local irreducible] DR.completeRSourceRead Expr.eval SourceNativeRootSemanticFaceAt.rootRead

theorem native_written_split : nativeUpdatedR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 nextPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame+
 nextNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame := by
 have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  (Mat.actual_writeback sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions) (F.fullWrite initial))
 have read := congrArg (fun environment : Env (CodeValue initial) C.Var => DR.completeRSourceRead initial 2 0 (environment () ())) written
 have value := (Mat.updated_total sourceFrame
  (programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).symm.trans
  (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updated_sum
 have result := read.trans (congrArg (fun value : CodeValue initial () =>
  DR.completeRSourceRead initial 2 0 (F.fullWrite initial value () ())) value)
 simpa only [nativeUpdatedR,nativeUpdatedRAt,nextPaR,nextNonPaR,F.fullWrite,map_add] using result

theorem native_pa_action : nextPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 RPhysical.variableAction observation nontrivial half
  (P.sourcePaInput (nextInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).pa_read

theorem native_nonPa_action : nextNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 RPhysical.variableAction observation nontrivial half
  (P.sourceNonPaInput (nextInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 (nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).nonPa_read

theorem whole_first : type_of% (Mat.whole_first sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := Mat.whole_first _ _ _

theorem target_next : type_of% (Mat.target_next sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := Mat.target_next _ _ _

theorem compiles : type_of% (Mat.compiles sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := Mat.compiles _ _ _

theorem successor_valid : type_of% (Mat.successor_valid sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := Mat.successor_valid _ _ _

theorem runtime_initial : type_of% (Mat.runtime_initial sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := Mat.runtime_initial _ _ _

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
