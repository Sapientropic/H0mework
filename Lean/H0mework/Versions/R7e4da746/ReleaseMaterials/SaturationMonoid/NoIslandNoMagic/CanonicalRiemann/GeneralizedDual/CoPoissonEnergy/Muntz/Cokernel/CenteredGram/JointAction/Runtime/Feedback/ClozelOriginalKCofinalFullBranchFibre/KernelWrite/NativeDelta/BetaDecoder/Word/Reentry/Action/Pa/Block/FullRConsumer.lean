import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRDivision

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
 (programme born material oldPaid code actualTrace lowBase selected nativeBorn nativeValue fullWrite actual_writeback
  inventory bornSegment born_pair_inventory whole_first target_next actual_receipt_next)
end F
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode
 (Value input code r p n u v twoAt)
end FC
namespace E
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullRBlockRelationWrite
 (npSource pnSource)
end E

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (BaseValue initial t) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (DR.L.Value (BaseValue initial) 2 t) :=
 DR.L.groups (BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t, AddCommGroup
 (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 t) :=
 DR.L.groups (DR.L.Value (BaseValue initial) 2) 0
local instance codeGroups (initial : Nat) : ∀ t, AddCommGroup (CodeValue initial t) :=
 DR.L.groups (BaseValue initial) 3
local instance valueGroups (initial : Nat) : ∀ t, AddCommGroup (FC.Value initial t) :=
 DR.L.groups (BaseValue initial) 5
local instance valueAddZeroClass (initial : Nat) (t : Unit) : AddZeroClass (FC.Value initial t) :=
 (valueGroups initial t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (initial : Nat) (t : Unit) : AddZero (FC.Value initial t) :=
 (valueAddZeroClass initial t).toAddZero

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))
local notation "body" => Block.sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "m" => F.material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "paid" => F.oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "native" => F.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "f" => F.born observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "cfg" => F.programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "low" => F.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "selected" => F.selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "effect" => F.nativeValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def nativeTrace : Trace ((m).environment+(m).increment)
 (.add (FC.code observation nontrivial half initial body) (.linear (-AddMonoidHom.id _) (.const paid)))
 (.const effect) := by
 have terminal : (selected).event.state.1 = .const effect :=
  (SourceGeneratedInquiryReceiptAction.Configured.Material.receipt f cfg low).2.1.2.down
 let actual : Trace (selected).rawRead.environment (selected).rawRead.expression (.const effect) :=
  Eq.mp (congrArg (fun terminal => Trace (selected).rawRead.environment (selected).rawRead.expression terminal) terminal)
   (selected).event.state.2
 have sameRaw : (selected).rawRead =
  (⟨(m).environment+(m).increment,
    RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression m⟩ :
   RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := FC.Value initial) (Var := C.Var) (sort := ())) :=
  (SourceGeneratedInquiryReceiptAction.Configured.Material.selected_raw f cfg low).trans rfl
 let moved := Eq.mp (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := FC.Value initial) (Var := C.Var) (sort := ()) =>
   Trace raw.environment raw.expression (.const effect)) sameRaw) actual
 change Trace _ (.add (m).raw (.linear (-AddMonoidHom.id _) (m).state.1)) _ at moved
 have old : (m).state.1 = .const paid :=
  SourceGeneratedInquiryReceiptAction.Configured.Writeback.old_paid_const f cfg
 have same := congrArg₂ (fun (raw terminal : Expr (FC.Value initial) C.Var ()) =>
  Expr.add raw (.linear (-AddMonoidHom.id _) terminal))
  (FullRSource.material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) old
 exact Eq.mp (congrArg (fun expression : Expr (FC.Value initial) C.Var () =>
  Trace ((m).environment+(m).increment) expression (.const effect)) same) moved

def rawSplit := (nativeTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).splitAdd
def rawValue := (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftValue
def receipts := FC.twoAt observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace

local notation "two" => receipts observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def sourceInput : CodeValue initial () := (Block.parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedPa +
 (Block.parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedNonPa
local notation "c" => sourceInput observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

theorem source_input (environment : Env (FC.Value initial) C.Var) :
 (FC.input initial body).eval environment = ((c,0),0) := rfl

private theorem source_r_lift (value : CodeValue initial ()) :
 FC.r observation nontrivial half initial ((value,0),0) =
 ((DR.completeRSourceAction observation nontrivial half initial 2 0 value,0),0) := by
 apply Prod.ext
 · apply Prod.ext
   · rfl
   · exact (DR.completeRSourceAction observation nontrivial half initial 2 0).map_zero
 · exact (pairLinear (Value := CodeValue initial)
    (DR.completeRSourceAction observation nontrivial half initial 2 0)).map_zero

theorem actual_full_action :
 rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 ((DR.completeRSourceAction observation nontrivial half initial 2 0 c,0),0) := by
 have action := FullRCode.TwoAt.full_action observation nontrivial half initial body
  ((m).environment+(m).increment)
  (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace
 rw [source_input] at action
 exact action.trans (source_r_lift observation nontrivial half initial c)

theorem actual_np_unit :
 (two).npValue = ((E.npSource observation nontrivial half initial c,0),0) := by
 have action := (two).np_unit
 rw [source_input] at action
 simpa only [FC.u,FullRCode.liftAction,pairLinear,AddMonoidHom.coe_prodMap,Prod.map_apply,Prod.map,map_zero] using action

theorem actual_pn_inverse :
 (two).pnValue = ((E.pnSource observation nontrivial half initial c,0),0) := by
 have action := (two).pn_inverse
 rw [source_input] at action
 simpa only [FC.v,FullRCode.liftAction,pairLinear,AddMonoidHom.coe_prodMap,Prod.map_apply,Prod.map,map_zero] using action

theorem actual_pa_physical : type_of% (FullRDivision.pa_physical observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two) :=
 FullRDivision.pa_physical observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two

theorem actual_pa_positionGap : type_of% (FullRDivision.pa_positionGap observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two) :=
 FullRDivision.pa_positionGap observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two

theorem actual_pa_response : type_of% (FullRDivision.pa_response observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two) :=
 FullRDivision.pa_response observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two

theorem actual_pa_unit_rank : type_of% (FullRDivision.pa_unit_rank observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two) :=
 FullRDivision.pa_unit_rank observation nontrivial half initial body
 ((m).environment+(m).increment)
 (rawValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (rawSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).leftTrace two

def writtenValue : FC.Value initial () := (native).activeEnvironment () ()

theorem written_full_value :
 writtenValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame =
 ((DR.completeRSourceAction observation nontrivial half initial 2 0 c,0),0) := by
 have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  (F.actual_writeback observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 have read := congrArg (fun environment : Env (FC.Value initial) C.Var => environment () ()) written
 have prefixEq := SourceGeneratedInquiryReceiptAction.Configured.Material.next_prefix_material f cfg low
 dsimp only [SourceGeneratedInquiryReceiptAction.Configured.Material.material] at read
 rw [prefixEq] at read
 change writtenValue observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame = _ at read
 rw [FullRSource.material_raw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame] at read
 have action := FullRCode.code_read observation nontrivial half initial body ((m).environment+(m).increment)
 rw [source_input] at action
 exact read.trans (action.trans (source_r_lift observation nontrivial half initial c))

theorem actual_occurrence_positions :
 (two).pa_input_retained.address ≠ (two).nonPa_input_retained.address := (two).source_occurrences_distinct

def npWritten :=
 (BornInventory.np observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).lift.transport
  (F.bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def pnWritten :=
 (BornInventory.pn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).lift.transport
  (F.bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

theorem np_written_word :
 (npWritten observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).word =
 liftMap (R := ℤ) (BornInventory.np observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).word := rfl

theorem pn_written_word :
 (pnWritten observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).word =
 liftMap (R := ℤ) (BornInventory.pn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).word := rfl

theorem prior_event_written (event : type_of% (BornInventory.inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).root)
 (member : event ∈ (BornInventory.inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trace) :
 T.liftEvent event ∈ (F.inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trace := by
 apply (F.bornSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).present
 unfold FullRSource.carriedSource
 rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.mapped_trace]
 exact List.mem_map_of_mem member

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
