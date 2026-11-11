import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Material.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit actualOccurrence queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw next)
end Q
namespace OI
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultAt resultLaw source_value)
end OI
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actualMaterial actionResultAt registered packetAt firstStep first_action occurrence afterEnvironment)
end R
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowProgramme)
end CF
namespace Mat
export SourceGeneratedInquiryReceiptAction.Configured.Material
 (generatedAction compiles whole_first target_next successor_valid nextMaterialFace next_prefix_result next_prefix_material runtime runtime_initial
  material nativeValue born updated_total native_effect native_inverse actual_writeback)
end Mat
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme)
end WB
local instance programmeGroups (initial : Nat) : ∀ target, AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance programmeBornGroups (initial : Nat) : ∀ target, AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance programmeRuntimeGroups (initial : Nat) : ∀ target, AddCommGroup
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
variable {current : J.Current sourceFrame.registered}
variable (supplied : I.Occurrence sourceFrame (current := current))

abbrev priorProgramme := SP.bornProgramme frame base before oldEnvironment admissions

def codeReader : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (PairValue (BaseValue initial)))) (Var := C.Var) (sort := ()) :=
 ⟨pairEnvironmentAt initial frame base before oldEnvironment admissions sourceFrame supplied,
  code observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied⟩

theorem code_reader_uniform
 {otherCurrent : J.Current sourceFrame.registered}
 (other : I.Occurrence sourceFrame (current := otherCurrent)) :
 codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied =
 codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame other := rfl

attribute [local irreducible] sourceRaw sourceEnvironment

def codeReceipt := OI.resultAt (Q.base sourceFrame).root.toAuthoritativeRoot
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) supplied

def codeResultLaw := OI.resultLaw (Q.base sourceFrame).root.toAuthoritativeRoot
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def fullSource := ((Q.root sourceFrame (priorProgramme initial frame base before oldEnvironment admissions)).source.base.withProjectionCoface
 (sourceLaw initial frame base before oldEnvironment admissions sourceFrame)).withProjectionCoface
 (codeResultLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

/-- The old complete projection law and both inherited inventories remain in the actual source programme. -/
def programme : A.Programme (PhysicalValue := PairValue (PairValue (BaseValue initial))) (PhysicalVar := C.Var) (sort := ()) :=
 { priorProgramme initial frame base before oldEnvironment admissions with
   datum := fun sourceFrame => {
    (priorProgramme initial frame base before oldEnvironment admissions).datum sourceFrame with
    component := some (fullSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).projectionLaw
    calculationReader := some (fun {_current} supplied =>
     codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied) } }

def componentInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Q.base sourceFrame).root.source.base
 (fullSource observation nontrivial half initial frame base before oldEnvironment admissions (A.epoch sourceFrame)).projectionLaw).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (Q.baseRoot sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base
  (Q.queryLaw (A.epoch sourceFrame) (programme observation nontrivial half initial frame base before oldEnvironment admissions))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (Q.queryRoot sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base
  (Q.resultLaw (A.epoch sourceFrame) (programme observation nontrivial half initial frame base before oldEnvironment admissions))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (Q.resultRoot sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base
  (Q.consumerLaw (A.epoch sourceFrame) (programme observation nontrivial half initial frame base before oldEnvironment admissions))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (Q.consumerRoot sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).source.base
  (Q.compilationLaw (A.epoch sourceFrame) (programme observation nontrivial half initial frame base before oldEnvironment admissions)))

def oldInstallation := ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (Q.root sourceFrame (priorProgramme initial frame base before oldEnvironment admissions)).source.base
 (sourceLaw initial frame base before oldEnvironment admissions (A.epoch sourceFrame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  ((Q.root sourceFrame (priorProgramme initial frame base before oldEnvironment admissions)).source.base.withProjectionCoface
   (sourceLaw initial frame base before oldEnvironment admissions (A.epoch sourceFrame)))
  (codeResultLaw observation nontrivial half initial frame base before oldEnvironment admissions (A.epoch sourceFrame)))).trans
 (componentInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def receiptInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 ((Q.root sourceFrame (priorProgramme initial frame base before oldEnvironment admissions)).source.base.withProjectionCoface
  (sourceLaw initial frame base before oldEnvironment admissions (A.epoch sourceFrame)))
 (codeResultLaw observation nontrivial half initial frame base before oldEnvironment admissions (A.epoch sourceFrame))).trans
 (componentInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def receiptFace : SourceNativeRootSemanticFaceAt
 (Q.root sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions))
 (Q.visit sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)) where
 projection := (receiptInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

abbrev born := SP.born frame base before oldEnvironment admissions
abbrev actualReceipt := R.actionResultAt (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (Q.actualOccurrence (born initial frame base before oldEnvironment admissions))
abbrev actualMaterial := R.actualMaterial (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)

abbrev fullUpdatedInput := DR.completeRSourceRead initial 2 0
 ((material initial frame base before oldEnvironment admissions).raw.eval
  ((material initial frame base before oldEnvironment admissions).environment+
   (material initial frame base before oldEnvironment admissions).increment),0)

abbrev receivedR := DR.completeRSourceRead initial 2 0
 (actualReceipt observation nontrivial half initial frame base before oldEnvironment admissions).2.2.1

theorem actual_receipt_value :
 (actualReceipt observation nontrivial half initial frame base before oldEnvironment admissions).2.2.1 =
 (code observation nontrivial half initial frame base before oldEnvironment admissions
  (born initial frame base before oldEnvironment admissions) (Q.actualOccurrence (born initial frame base before oldEnvironment admissions))).eval
 (pairEnvironmentAt initial frame base before oldEnvironment admissions
  (born initial frame base before oldEnvironment admissions) (Q.actualOccurrence (born initial frame base before oldEnvironment admissions))) :=
 OI.source_value _ _ _

theorem received_R_action : receivedR observation nontrivial half initial frame base before oldEnvironment admissions =
 RPhysical.variableAction observation nontrivial half (fullUpdatedInput initial frame base before oldEnvironment admissions) :=
 (congrArg (DR.completeRSourceRead initial 2 0)
  (actual_receipt_value observation nontrivial half initial frame base before oldEnvironment admissions)).trans
 (actual_full_update observation nontrivial half initial frame base before oldEnvironment admissions)

abbrev nativeRequest := R.registered (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
def fullWrite (value : PairValue (PairValue (PairValue (BaseValue initial))) ()) :
 Env (PairValue (PairValue (PairValue (BaseValue initial)))) C.Var :=
 fun target _ => by cases target; exact value

abbrev lowBase := WB.programme (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions) (fullWrite initial)

abbrev generatedAction := Mat.generatedAction (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)

abbrev nativeRuntime := Mat.runtime (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)

theorem native_runtime_initial : type_of% (Mat.runtime_initial
 (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)) := Mat.runtime_initial _ _ _

theorem native_first : type_of% (R.first_action (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)) := R.first_action _ _

theorem whole_first : type_of% (Mat.whole_first (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)) := Mat.whole_first _ _ _

theorem canonical_next : type_of% (Mat.target_next (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)) := Mat.target_next _ _ _

abbrev nextReceiptFace := Mat.nextMaterialFace
 (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)

abbrev nextSourceOccurrence := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
 (nativeRequest observation nontrivial half initial frame base before oldEnvironment admissions)
 (R.packetAt (born initial frame base before oldEnvironment admissions)
  (programme observation nontrivial half initial frame base before oldEnvironment admissions))
 ((generatedAction observation nontrivial half initial frame base before oldEnvironment admissions).target.targetRoot.emitted
  (generatedAction observation nontrivial half initial frame base before oldEnvironment admissions).target.targetVisit.current)

theorem next_receipt_value :
 (nextReceiptFace observation nontrivial half initial frame base before oldEnvironment admissions).rootRead.prefixResult.2.2.1 =
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions
  (born initial frame base before oldEnvironment admissions) (Q.actualOccurrence (born initial frame base before oldEnvironment admissions))).expression.eval
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions
  (born initial frame base before oldEnvironment admissions) (Q.actualOccurrence (born initial frame base before oldEnvironment admissions))).environment := by
 change (Mat.nextMaterialFace
  (born initial frame base before oldEnvironment admissions)
  (programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)).rootRead.prefixResult.2.2.1 = _
 rw [Mat.next_prefix_result]
 exact actual_receipt_value observation nontrivial half initial frame base before oldEnvironment admissions

abbrev nextReceivedR := DR.completeRSourceRead initial 2 0
 (nextReceiptFace observation nontrivial half initial frame base before oldEnvironment admissions).rootRead.prefixResult.2.2.1

theorem next_received_R_action : nextReceivedR observation nontrivial half initial frame base before oldEnvironment admissions =
 RPhysical.variableAction observation nontrivial half (fullUpdatedInput initial frame base before oldEnvironment admissions) :=
 (congrArg (DR.completeRSourceRead initial 2 0)
  (next_receipt_value observation nontrivial half initial frame base before oldEnvironment admissions)).trans
 (actual_full_update observation nontrivial half initial frame base before oldEnvironment admissions)

theorem native_compiles : type_of% (Mat.compiles (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)) := Mat.compiles _ _ _

theorem native_successor_valid : type_of% (Mat.successor_valid (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)) := Mat.successor_valid _ _ _

private theorem code_expression_frame
 (otherFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))
 {otherCurrent : J.Current otherFrame.registered}
 (other : I.Occurrence otherFrame (current := otherCurrent)) :
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied).expression =
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions otherFrame other).expression := by
 unfold codeReader code sourceRaw source sourceLaw sourceAt
 rfl

private abbrev lowBaseAt := WB.programme sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions) (fullWrite initial)

private def nativeBornAt := Mat.born sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBaseAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

private def nativeUpdatedRAt : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 ((nativeBornAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).activeEnvironment () ())

attribute [local irreducible] DR.completeRSourceRead Expr.eval SourceNativeRootSemanticFaceAt.rootRead

private theorem native_written_full_value_at :
 nativeUpdatedRAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 DR.completeRSourceRead initial 2 0
 ((R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).raw.eval
  ((R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).environment+
   (R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).increment)) := by
 have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  (Mat.actual_writeback sourceFrame
   (programme observation nontrivial half initial frame base before oldEnvironment admissions) (fullWrite initial))
 have read := congrArg (fun env : Env (PairValue (PairValue (PairValue (BaseValue initial)))) C.Var =>
  DR.completeRSourceRead initial 2 0 (env () ())) written
 have retained := congrArg (fun m : type_of% (R.actualMaterial sourceFrame
    (programme observation nontrivial half initial frame base before oldEnvironment admissions)) =>
   DR.completeRSourceRead initial 2 0 (fullWrite initial (m.raw.eval (m.environment+m.increment)) () ()))
  (Mat.next_prefix_material sourceFrame
   (programme observation nontrivial half initial frame base before oldEnvironment admissions)
   (lowBaseAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 simpa only [nativeUpdatedRAt, nativeBornAt, lowBaseAt, fullWrite] using read.trans retained

private def sourceActionNextAt := Q.next sourceFrame
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)

private def updatedSourceInputAt : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0
 ((sourceRaw initial frame base before oldEnvironment admissions
   (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
   (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))).expression.eval
  (sourceEnvironment initial frame base before oldEnvironment admissions
   (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
   (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))),0)

private theorem native_updated_R_action_at :
 nativeUpdatedRAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 RPhysical.variableAction observation nontrivial half
 (updatedSourceInputAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 refine (native_written_full_value_at observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trans ?_
 have raw : (R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).raw =
   (codeReader observation nontrivial half initial frame base before oldEnvironment admissions
    (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
    (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))).expression :=
  code_expression_frame observation nontrivial half initial frame base before oldEnvironment admissions
   (A.epoch sourceFrame) (R.occurrence sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions))
   (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
   (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 have env : (R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).environment+
   (R.actualMaterial sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)).increment =
   (codeReader observation nontrivial half initial frame base before oldEnvironment admissions
    (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
    (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))).environment := by
  change _+(R.afterEnvironment sourceFrame
   (programme observation nontrivial half initial frame base before oldEnvironment admissions)-_) =
   R.afterEnvironment sourceFrame (programme observation nontrivial half initial frame base before oldEnvironment admissions)
  exact add_sub_cancel _ _
 rw [raw,env]
 exact source_read observation nontrivial half initial frame base before oldEnvironment admissions
  (A.epoch (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
  (Q.actualOccurrence (sourceActionNextAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))

attribute [local irreducible] nativeUpdatedRAt updatedSourceInputAt

abbrev nativeBorn := Mat.born (born initial frame base before oldEnvironment admissions)
 (programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)

/-- The read is generated from the actual full writer, with its typed frame kept abstract during elaboration. -/
def nativeUpdatedR : PairValue (PairValue C.Value) () :=
 nativeUpdatedRAt observation nontrivial half initial frame base before oldEnvironment admissions
 (born initial frame base before oldEnvironment admissions)

def updatedSourceInput : PairValue (PairValue C.Value) () :=
 updatedSourceInputAt observation nontrivial half initial frame base before oldEnvironment admissions
 (born initial frame base before oldEnvironment admissions)

theorem native_full_write : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
 (nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions)
 (fullWrite initial
  ((Mat.material (born initial frame base before oldEnvironment admissions)
    (programme observation nontrivial half initial frame base before oldEnvironment admissions)
    (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)).raw.eval
   ((Mat.material (born initial frame base before oldEnvironment admissions)
     (programme observation nontrivial half initial frame base before oldEnvironment admissions)
     (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)).environment+
    (Mat.material (born initial frame base before oldEnvironment admissions)
     (programme observation nontrivial half initial frame base before oldEnvironment admissions)
     (lowBase observation nontrivial half initial frame base before oldEnvironment admissions)).increment))) :=
 Mat.actual_writeback _ _ _

theorem native_updated_R_action : nativeUpdatedR observation nontrivial half initial frame base before oldEnvironment admissions =
 RPhysical.variableAction observation nontrivial half
 (updatedSourceInput observation nontrivial half initial frame base before oldEnvironment admissions) :=
 native_updated_R_action_at observation nontrivial half initial frame base before oldEnvironment admissions
 (born initial frame base before oldEnvironment admissions)

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
