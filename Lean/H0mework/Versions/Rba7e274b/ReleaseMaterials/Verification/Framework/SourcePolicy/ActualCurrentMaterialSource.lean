import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCurrentMaterialSourceVerification
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceFamilyActualCurrentMaterialEnvironmentUpdate
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (actual_inverse generated_differential whole_recovery FullWord)
end F

section SourceControls
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))
example : (reader (A.epoch frame) supplied).expression = liftExpr (AN.paid frame).raw :=
 reader_paid_raw frame supplied
def source_trace_control : Trace (reader frame supplied).environment (reader frame supplied).expression
 (.const (I.materialAt frame supplied).pair) := reader_trace frame supplied
example (settled : (RootGeneratedDebtActivationJointSource.mathAction
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current.2).isLeft = true) :
 (reader (A.epoch frame) (S.actualOccurrence frame)).environment =
 pairEnvironment (AN.paid frame).environment (AN.paid frame).increment :=
 reader_paid_environment frame settled
end SourceControls

section FactoryControls
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance groups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s) (n : Nat) (seed : SF.Seed W X s n)
variable (frame : M.Frame (Value := L.Value W n) (Var := X) (sort := s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))
example : (datum factory n seed frame).calculationReader =
 some (fun {current} supplied => reader frame (current := current) supplied) := rfl
example : (datum factory n seed frame).reader (current := current) supplied =
 (factory.datum n seed frame).reader (current := current) supplied := rfl
example : type_of% (query_action_raw factory n seed frame supplied) := query_action_raw _ _ _ _ _
example : type_of% (query_value factory n seed frame) := query_value _ _ _ _
example : type_of% (Q.common_classifier frame (SF.cfg (update factory) n seed)) := Q.common_classifier _ _
example : type_of% (Q.stock_retained frame (SF.cfg (update factory) n seed)) := Q.stock_retained _ _
end FactoryControls

section NativeControls
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance nativeGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (generated : NativeMaterial factory packet)
example : type_of% generated.source_ast := generated.source_ast
example : type_of% generated.source_environment := generated.source_environment
def native_material_control : NativeMaterial factory packet := nativeMaterial factory packet
example : type_of% (F.actual_inverse (AN.paid generated.frame)) := F.actual_inverse _
example : type_of% (F.generated_differential (AN.paid generated.frame)) := F.generated_differential _
example (word : Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s) :
 type_of% (F.whole_recovery (AN.paid generated.frame) word) := F.whole_recovery _ _
example : type_of% (Native.native_packet_actual (queryFactory factory) packet) := Native.native_packet_actual _ _
example : type_of% (Native.receiver_input (queryFactory factory) packet) := Native.receiver_input _ _
end NativeControls

section RootControls
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance requestGroups : (t : Sorts) → AddCommGroup
 (Future.NativeValue (queryFactory factory) initial sourceCfg language (ordinal+1) t) :=
 fun t => L.groups W (D.packetAt (queryFactory factory) initial sourceCfg language (ordinal+1)).1 t
def integrated_consumer_control : type_of% (ActualCofinalRootResidualConsumer.consume (queryFactory factory)
 initial sourceCfg language ordinal) :=
 consume_actual factory initial sourceCfg language ordinal
  (fun _material request _current model _future compiled whole =>
   ⟨request, ⟨model⟩, ⟨compiled⟩, ⟨whole⟩⟩)
example : type_of% (ActualCofinalRootResidualConsumer.rooted_material_source
 (queryFactory factory) initial sourceCfg language ordinal) :=
 ActualCofinalRootResidualConsumer.rooted_material_source _ _ _ _ _
example : type_of% (Native.actual_next_packet (queryFactory factory)
 initial sourceCfg language ordinal) := Native.actual_next_packet _ _ _ _ _
end RootControls

section ShadowControl
abbrev V (_ : Unit) := ℤ
abbrev X (_ : Unit) := Unit
def env : Env V X := fun _ _ => 0
def code : Expr V X () := .const 7
example : (liftExpr code).eval (pairEnvironment env 0) = ((7 : ℤ), 0) := rfl
example : relationMap (R := ℤ) env ((execution env code).relationWords (R := ℤ)) = 0 := rfl
example : (liftExpr code).eval (pairEnvironment env 0) ≠ ((0 : ℤ), 0) := by decide
end ShadowControl
end ActualCurrentMaterialSourceVerification
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
