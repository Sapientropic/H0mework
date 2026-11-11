import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Relation.Install

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift

namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material
 (generatedAction runtime runtime_initial nextMaterialFace material oldPaid nativeValue receipt selected born
  old_paid_const selected_raw actual_writeback updated_total native_effect native_inverse
  whole_first target_next compiles successor_valid)
end M

namespace RI
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullRBlockRelationInstall
 (PairInventory pairWritten pairWritten_trace pairWritten_preserves pair_np_occurrence pair_pn_occurrence)
end RI

namespace T
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (liftEvent)
end T


section Assembly
variable {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
variable (baseProgramme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
variable (law : (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
 SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource)
variable (reader : (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
 {current : J.Current receiver.registered} → I.Occurrence receiver (current := current) →
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue Value) (Var := baseProgramme.LowVar) (sort := ()))
variable (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ()))

private def assembleSource := (S.root receiver baseProgramme).source.base.withProjectionCoface (law receiver)
private def assemble : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) :=
 { baseProgramme with datum := fun receiver => { baseProgramme.datum receiver with
   component := some (assembleSource baseProgramme law receiver).projectionLaw
   calculationReader := some (reader receiver) } }

private def assembleComponent := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.base receiver).root.source.base (assembleSource baseProgramme law (A.epoch receiver)).projectionLaw).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot receiver (assemble baseProgramme law reader)).source.base
  (S.queryLaw (A.epoch receiver) (assemble baseProgramme law reader))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot receiver (assemble baseProgramme law reader)).source.base
  (S.resultLaw (A.epoch receiver) (assemble baseProgramme law reader))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot receiver (assemble baseProgramme law reader)).source.base
  (S.consumerLaw (A.epoch receiver) (assemble baseProgramme law reader))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot receiver (assemble baseProgramme law reader)).source.base
  (S.compilationLaw (A.epoch receiver) (assemble baseProgramme law reader)))

private def assembleOld := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (S.root receiver baseProgramme).source.base (law (A.epoch receiver))).trans
 (assembleComponent baseProgramme law reader receiver)
private def assembleInstalled := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.root receiver baseProgramme).source.base (law (A.epoch receiver))).trans
 (assembleComponent baseProgramme law reader receiver)
end Assembly


section CompletedSplice
variable {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
variable (prefixFrame : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ()))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
variable (lowProgramme : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := ()))
variable (currentFrame : Reentry.A.M.Frame (Value := PairValue Value) (Var := cfg.LowVar) (sort := ()))

private def matFaceAt : SourceNativeRootSemanticFaceAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn currentFrame
  (M.programme prefixFrame cfg lowProgramme)).old.root
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn currentFrame
  (M.programme prefixFrame cfg lowProgramme)).old.visit where
 projection := (M.prefixInstallation prefixFrame cfg lowProgramme currentFrame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

private def matReadAt : SourceGeneratedInquiryReceiptAction.Configured.Material.SourceAt
 prefixFrame cfg (A.epoch currentFrame) (S.actualOccurrence currentFrame) :=
 (matFaceAt prefixFrame cfg lowProgramme currentFrame).rootRead

private theorem mat_read_at : HEq
 (matFaceAt prefixFrame cfg lowProgramme currentFrame).rootRead
 (matReadAt prefixFrame cfg lowProgramme currentFrame) := HEq.rfl

private theorem mat_state_at : HEq
 (matReadAt prefixFrame cfg lowProgramme currentFrame).currentMaterial.paid.state
 currentFrame.event.state := HEq.rfl

private theorem mat_trace_at : HEq
 (matReadAt prefixFrame cfg lowProgramme currentFrame).currentMaterial.paid.state.2
 currentFrame.event.state.2 := HEq.rfl

private theorem mat_raw_at :
 (⟨(matReadAt prefixFrame cfg lowProgramme currentFrame).currentMaterial.paid.environment,
   (matReadAt prefixFrame cfg lowProgramme currentFrame).currentMaterial.paid.raw⟩ :
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := PairValue Value) (Var := cfg.LowVar) (sort := ())) = currentFrame.rawRead := rfl
private theorem mat_initial_raw : (M.initial prefixFrame cfg).rawRead =
 (⟨(M.material prefixFrame cfg lowProgramme).environment+(M.material prefixFrame cfg lowProgramme).increment,
   RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
    (M.material prefixFrame cfg lowProgramme)⟩ :
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := PairValue Value) (Var := cfg.LowVar) (sort := ())) := rfl

private theorem mat_terminal_at (value : PairValue Value ())
 (terminal : currentFrame.event.state.1=.const value) :
 (matReadAt prefixFrame cfg lowProgramme currentFrame).currentMaterial.paid.state.1=.const value := terminal
end CompletedSplice



local instance blockProgrammeBaseGroups (initial : Nat) : ∀ target,AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance blockProgrammeOriginGroups (initial : Nat) : ∀ target,AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance blockProgrammeRuntimeGroups (initial : Nat) : ∀ target,AddCommGroup
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

local notation "K" => parentProgramme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "B" => parentBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "parent" => parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "Law" => (fun receiver => sourceLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver)
local notation "Reader" => (fun receiver {_current} supplied => codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied)

variable (receiver : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ()))

def fullSource := assembleSource K Law receiver



def sourceRelationBody : Expr (CodeValue initial) C.Var () :=
 .const ((parent).updatedPa + (parent).updatedNonPa)

def sourcePairInventory : RI.PairInventory initial C.Var :=
 RI.pairWritten initial C.Var observation nontrivial half
  (((K).nextPairInventory receiver).get (by rfl))
  (sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def programme : A.Programme (PhysicalValue := CodeValue initial) (PhysicalVar := C.Var) (sort := ()) :=
 let assembled := assemble K Law Reader
 let written := fun receiver =>
   (assembled.nextPairInventory receiver).map (fun source =>
     RI.pairWritten initial C.Var observation nontrivial half source
      (sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 { assembled with
   datum := fun receiver =>
     { assembled.datum receiver with
       nextPairInventoryAt := some (fun {_current} _supplied =>
         some ((sourcePairInventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).map
           (T.liftEvent (PhysicalValue := PairValue (CodeValue initial))
             (PhysicalVar := C.Var) (sort := ())))) }
   nextPairInventory := written }



local notation "Cfg" => programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def componentInstallation := assembleComponent K Law Reader receiver




def sourceInstallation := assembleInstalled K Law Reader receiver



def fullWrite (value : BlockValue initial ()) : Env (BlockValue initial) C.Var :=
 fun target _ => by cases target; exact value



abbrev lowBase := WB.programme B Cfg (fullWrite initial)


abbrev generatedAction := M.generatedAction B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)


abbrev runtime := M.runtime B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)


abbrev nextReceiptFace := M.nextMaterialFace B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)



private def sourceFaceAt : SourceNativeRootSemanticFaceAt (S.root receiver Cfg) (S.visit receiver Cfg) where
 projection := (sourceInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl



private def sourceReadAt : SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
 (A.epoch receiver) (S.actualOccurrence receiver) :=
 (sourceFaceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).rootRead



private theorem source_read_legs_at :
 (sourceReadAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).legs = parent := by
 let installed := sourceInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver
 have carried := installed.outcome_heq (S.actualOccurrence receiver) PUnit.unit
 have same : (Sum.inl ⟨PUnit.unit,
    sourceReadAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver⟩ :
   (Sigma fun _ : PUnit => SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
     (A.epoch receiver) (S.actualOccurrence receiver)) ⊕ PEmpty) =
   Sum.inl ⟨PUnit.unit,
    sourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
     (A.epoch receiver) (S.actualOccurrence receiver)⟩ := eq_of_heq carried
 exact congrArg (fun value : Sigma fun _ : PUnit => SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
    (A.epoch receiver) (S.actualOccurrence receiver) => value.2.legs) (Sum.inl.inj same)



abbrev sourceFace := sourceFaceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame B


abbrev sourceMaterial := sourceReadAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame B



theorem source_parent_legs :
 (sourceMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).legs = parent :=
 source_read_legs_at observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame B



def material := M.material B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def oldPaid : BlockValue initial () :=
 (nextReceiptFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead.prefixResult.2.2.1
def nativeValue : BlockValue initial () := M.nativeValue B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev receipt := M.receipt B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev selected := M.selected B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
abbrev nativeBorn := M.born B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def inheritedPairInventory
 (receiver : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ())) :
 Option (RI.PairInventory initial C.Var) :=
 (parentProgramme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).nextPairInventory
  receiver

theorem pair_inventory_written
 (receiver : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ())) :
 (Cfg).nextPairInventory receiver =
  (inheritedPairInventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).map
   (fun source => RI.pairWritten initial C.Var observation nontrivial half source
    (sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := by
 rfl

abbrev nextCompletedFace := matFaceAt B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

abbrev nextCompletedMaterial := matReadAt B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

theorem next_completed_read : HEq
 (nextCompletedFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead
 (nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 mat_read_at B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) _

theorem next_completed_state : HEq
 (nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).currentMaterial.paid.state
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state :=
 mat_state_at B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) _

theorem next_completed_trace : HEq
 (nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).currentMaterial.paid.state.2
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state.2 :=
 mat_trace_at B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) _

theorem next_completed_raw :
 (⟨(nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).currentMaterial.paid.environment,
   (nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).currentMaterial.paid.raw⟩ :
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := BlockValue initial) (Var := C.Var) (sort := ())) =
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rawRead :=
 mat_raw_at B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) _

theorem material_raw : (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).raw =
 codeAt initial (parent).updatedPa (parent).updatedNonPa := rfl

theorem old_paid_const :
 (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).state.1 =
 .const (oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := M.old_paid_const _ _ _

theorem native_terminal :
 (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state.1 =
 .const (nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (receipt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).2.1.2.down

theorem initial_raw : type_of% (mat_initial_raw B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 mat_initial_raw B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

private theorem material_heq : HEq
 (M.material B Cfg
   (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 (material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := HEq.rfl

private def closeTrace {environment : Env (BlockValue initial) C.Var}
 {expression : Expr (BlockValue initial) C.Var ()}
 (state : SourceOperationExecutionDebt.State environment expression) (value : BlockValue initial ())
 (paid : state.1=.const value) : Trace environment expression (.const value) :=
 Eq.mp (congrArg (fun terminal => Trace environment expression terminal) paid) state.2

section NativeTransport
attribute [local irreducible] material oldPaid nativeValue
local notation "m" => material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "old" => oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "delta" => nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def oldTrace : Trace (m).environment (codeAt initial (parent).updatedPa (parent).updatedNonPa) (.const old) :=
 Eq.mp (congrArg (fun expression : Expr (BlockValue initial) C.Var () => Trace (m).environment expression (.const old))
  (material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 (closeTrace initial (m).state old (old_paid_const observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))

def nativeTrace : Trace ((m).environment+(m).increment)
 (.add (codeAt initial (parent).updatedPa (parent).updatedNonPa)
  (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) (.const old))) (.const delta) := by
 let observed := (nextCompletedMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).currentMaterial.paid
 have terminal : observed.state.1=.const delta :=
  mat_terminal_at B Cfg (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
   (selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) delta
   (native_terminal observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 let actual := closeTrace initial
  observed.state delta terminal
 have sourceRaw := (next_completed_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trans ((M.selected_raw B Cfg
  (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).trans
  (initial_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 let moved := Eq.mp (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := BlockValue initial) (Var := C.Var) (sort := ()) =>
    Trace raw.environment raw.expression (.const delta)) sourceRaw) actual
 have fromInitial := congrArg
  (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := BlockValue initial) (Var := C.Var) (sort := ()) => raw.expression)
  (mat_initial_raw B Cfg
   (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame))
 have expressionEq := congrArg₂ (fun (raw terminal : Expr (BlockValue initial) C.Var ()) =>
  Expr.add raw (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) terminal))
  (material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  (old_paid_const observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 have fromInitial' :
   (M.initial B Cfg).rawRead.expression =
    (M.material B Cfg
      (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).raw.add
      (.linear (s:=()) (t:=()) (-AddMonoidHom.id _)
       (M.material B Cfg
        (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).state.1) := by
  simpa only [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression] using fromInitial
 have materialRawEq :
   (M.material B Cfg
      (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).raw = (m).raw := by
  have materialEq :
    M.material B Cfg
      (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) = (m) :=
   eq_of_heq (material_heq observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  exact congrArg (fun value => value.raw) materialEq
 have materialStateEq :
   (M.material B Cfg
      (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).state.1 = (m).state.1 := by
  have materialEq :
    M.material B Cfg
      (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) = (m) :=
   eq_of_heq (material_heq observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  exact congrArg (fun value => value.state.1) materialEq
 have expressionFromInitial :
   (M.initial B Cfg).rawRead.expression =
    (.add (m).raw (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) (m).state.1)) :=
  fromInitial'.trans (congrArg₂
   (fun (raw terminal : Expr (BlockValue initial) C.Var ()) =>
    Expr.add raw (.linear (s:=()) (t:=()) (-AddMonoidHom.id _) terminal))
   materialRawEq materialStateEq)
 have fullExpression := expressionFromInitial.trans expressionEq
 have materialEq :
   M.material B Cfg
     (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) = (m) :=
  eq_of_heq (material_heq observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 have moved' : Trace ((m).environment+(m).increment)
   (M.initial B Cfg).rawRead.expression (.const delta) :=
  Eq.mp (congrArg (fun value =>
    Trace (value.environment + value.increment)
      (M.initial B Cfg).rawRead.expression (.const delta)) materialEq) moved
 exact Eq.mp (congrArg (fun expression : Expr (BlockValue initial) C.Var () =>
  Trace ((m).environment+(m).increment) expression (.const delta)) fullExpression) moved'

def nextOldFourAt := fourAt initial (parent).updatedPa (parent).updatedNonPa (m).environment old
 (oldTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
def nextNativeSplit := Trace.splitAdd
 (nativeTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
def nextFourAt := fourAt initial (parent).updatedPa (parent).updatedNonPa ((m).environment+(m).increment)
 (nextNativeSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftValue
 (nextNativeSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace
end NativeTransport



attribute [local irreducible] nextFourAt

local notation "m" => material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "four" => nextFourAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "outer" => nextNativeSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "origin" => SourceAt.legs (sourceMaterial observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def blockRead : BlockValue initial () →+ PairValue (PairValue C.Value) () :=
 (DR.completeRSourceRead initial 2 0).comp ((AddMonoidHom.fst _ _)+(AddMonoidHom.snd _ _))

def parentInput : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0 (origin).fullInput
def parentPaR : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0 (origin).updatedPa
def parentNonPaR : PairValue (PairValue C.Value) () := DR.completeRSourceRead initial 2 0 (origin).updatedNonPa
def parentReceived : PairValue (PairValue C.Value) () :=
 DR.completeRSourceRead initial 2 0 ((origin).updatedPa+(origin).updatedNonPa)

theorem parent_pa_action : parentPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 RPhysical.variableAction observation nontrivial half
  (P.sourcePaInput (parentInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := (origin).pa_read

theorem parent_nonPa_action : parentNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 RPhysical.variableAction observation nontrivial half
  (P.sourceNonPaInput (parentInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := (origin).nonPa_read

theorem parent_split : parentReceived observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 parentPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame+
 parentNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame := map_add _ _ _

def nextPP : PairValue (PairValue C.Value) () := blockRead initial (four).pp
def nextNP : PairValue (PairValue C.Value) () := blockRead initial (four).np
def nextPN : PairValue (PairValue C.Value) () := blockRead initial (four).pn
def nextNN : PairValue (PairValue C.Value) () := blockRead initial (four).nn
def nativeUpdatedR : PairValue (PairValue C.Value) () := blockRead initial
 ((nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).activeEnvironment () ())

theorem native_pp_action : nextPP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 P.sourcePaInput (parentPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 have action : nextPP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
   DR.completeRSourceRead initial 2 0 (P.sourcePaLift initial 2 0 (parent).updatedPa) := by
  change blockRead initial (four).pp = _
  rw [(four).pp_action]
  change DR.completeRSourceRead initial 2 0 (P.sourcePaLift initial 2 0 (parent).updatedPa+0) = _
  rw [add_zero]
 have fixed := congrArg (fun legs : type_of% (parent) => DR.completeRSourceRead initial 2 0 legs.updatedPa)
  (source_parent_legs observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 exact action.trans ((P.source_Pa_lift_read initial 2 0 (parent).updatedPa).trans (congrArg P.sourcePaInput fixed.symm))

theorem native_np_action : nextNP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 P.sourceNonPaInput (parentPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 have action : nextNP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
   DR.completeRSourceRead initial 2 0 (P.sourceNonPaLift initial 2 0 (parent).updatedPa) := by
  change blockRead initial (four).np = _
  rw [(four).np_action]
  change DR.completeRSourceRead initial 2 0 (P.sourceNonPaLift initial 2 0 (parent).updatedPa+0) = _
  rw [add_zero]
 have fixed := congrArg (fun legs : type_of% (parent) => DR.completeRSourceRead initial 2 0 legs.updatedPa)
  (source_parent_legs observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 exact action.trans ((P.source_nonPa_lift_read initial 2 0 (parent).updatedPa).trans (congrArg P.sourceNonPaInput fixed.symm))

theorem native_pn_action : nextPN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 P.sourcePaInput (parentNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 have action : nextPN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
   DR.completeRSourceRead initial 2 0 (P.sourcePaLift initial 2 0 (parent).updatedNonPa) := by
  change blockRead initial (four).pn = _
  rw [(four).pn_action]
  change DR.completeRSourceRead initial 2 0 (P.sourcePaLift initial 2 0 (parent).updatedNonPa+0) = _
  rw [add_zero]
 have fixed := congrArg (fun legs : type_of% (parent) => DR.completeRSourceRead initial 2 0 legs.updatedNonPa)
  (source_parent_legs observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 exact action.trans ((P.source_Pa_lift_read initial 2 0 (parent).updatedNonPa).trans (congrArg P.sourcePaInput fixed.symm))

theorem native_nn_action : nextNN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 P.sourceNonPaInput (parentNonPaR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 have action : nextNN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
   DR.completeRSourceRead initial 2 0 (P.sourceNonPaLift initial 2 0 (parent).updatedNonPa) := by
  change blockRead initial (four).nn = _
  rw [(four).nn_action]
  change DR.completeRSourceRead initial 2 0 (P.sourceNonPaLift initial 2 0 (parent).updatedNonPa+0) = _
  rw [add_zero]
 have fixed := congrArg (fun legs : type_of% (parent) => DR.completeRSourceRead initial 2 0 legs.updatedNonPa)
  (source_parent_legs observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 exact action.trans ((P.source_nonPa_lift_read initial 2 0 (parent).updatedNonPa).trans (congrArg P.sourceNonPaInput fixed.symm))

theorem native_raw_value : (m).raw.eval ((m).environment+(m).increment) = (outer).leftValue :=
 (congrArg (fun expression : Expr (BlockValue initial) C.Var () => expression.eval ((m).environment+(m).increment))
  (material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).trans
 (completed_trace_value ((m).environment+(m).increment) (outer).leftTrace).symm

theorem native_written_four : nativeUpdatedR observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 (nextPP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame+
   nextNP observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)+
 (nextPN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame+
   nextNN observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  (M.actual_writeback B Cfg (fullWrite initial))
 have read := congrArg (fun environment : Env (BlockValue initial) C.Var => blockRead initial (environment () ())) written
 have generated := (native_raw_value observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trans (four).sum
 have result := read.trans (congrArg (fun value : BlockValue initial () => blockRead initial (fullWrite initial value () ())) generated)
 simpa only [nativeUpdatedR,fullWrite,map_add,nextPP,nextNP,nextPN,nextNN] using result

theorem native_effect : type_of% (M.native_effect B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.native_effect _ _ _
theorem native_inverse : type_of% (M.native_inverse B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.native_inverse _ _ _
theorem actual_receipt_next : type_of% (M.actual_receipt_next B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.actual_receipt_next _ _ _
theorem actual_receipt_compiles : type_of% (M.actual_receipt_compiles B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.actual_receipt_compiles _ _ _
theorem whole_first : type_of% (M.whole_first B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.whole_first _ _ _
theorem target_next : type_of% (M.target_next B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.target_next _ _ _
theorem compiles : type_of% (M.compiles B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.compiles _ _ _
theorem successor_valid : type_of% (M.successor_valid B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.successor_valid _ _ _
theorem runtime_initial : type_of% (M.runtime_initial B Cfg
 (lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) := M.runtime_initial _ _ _


end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
