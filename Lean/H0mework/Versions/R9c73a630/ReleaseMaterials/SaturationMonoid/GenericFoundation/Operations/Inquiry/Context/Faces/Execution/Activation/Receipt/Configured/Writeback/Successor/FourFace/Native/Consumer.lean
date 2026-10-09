import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
private def transportTrace {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ s, AddCommGroup (Value s)] {sort : Sorts}
    {old new : Env Value Var} {before first after last : Expr Value Var sort}
    (trace : Trace old before after) (envEq : old = new) (beforeEq : before = first) (afterEq : after = last) :
    Trace new first last := by
 cases envEq; cases beforeEq; cases afterEq; exact trace
private theorem transportTrace_heq {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ s, AddCommGroup (Value s)] {sort : Sorts}
    {old new : Env Value Var} {before first after last : Expr Value Var sort}
    (trace : Trace old before after) (envEq : old = new) (beforeEq : before = first) (afterEq : after = last) :
    HEq (transportTrace trace envEq beforeEq afterEq) trace := by
 cases envEq; cases beforeEq; cases afterEq; rfl

section ActualReceipt
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {sort : Sorts}
local instance actualLevelGroups (n : Nat) (s : Sorts) : AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value Value n s) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.groups Value n s
variable (factory : AS.SF.Factory Value Var sort)
variable (sourceFrame : A.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (language : cfg.LowVar = Var)
abbrev sourceMaterial := SourceGeneratedInquiryReceiptAction.actualMaterial sourceFrame cfg
abbrev selected := AS.firstSelected factory sourceFrame cfg language
abbrev receipt := AS.firstReceipt factory sourceFrame cfg language
abbrev nativeValue := (receipt factory sourceFrame cfg language).2.1.1
abbrev nativeMaterial := paid (selected factory sourceFrame cfg language)

namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
abbrev nativeInput := (selected factory sourceFrame cfg language).registered.input

theorem selected_endpoint : (selected factory sourceFrame cfg language).event.state.1 =
 .const (nativeValue factory sourceFrame cfg language) := (receipt factory sourceFrame cfg language).2.1.2.down

def nativeTrace : Trace (nativeInput factory sourceFrame cfg language).environment
 (nativeInput factory sourceFrame cfg language).expression (.const (nativeValue factory sourceFrame cfg language)) :=
 transportTrace (selected factory sourceFrame cfg language).event.state.2 rfl rfl
  (selected_endpoint factory sourceFrame cfg language)

theorem native_trace_actual : HEq (nativeTrace factory sourceFrame cfg language)
 (selected factory sourceFrame cfg language).event.state.2 := transportTrace_heq _ _ _ _

theorem native_value : nativeValue factory sourceFrame cfg language =
 (nativeInput factory sourceFrame cfg language).expression.eval
 (nativeInput factory sourceFrame cfg language).environment := (nativeTrace factory sourceFrame cfg language).sound.symm

theorem new_literal_boundary : F.boundary (nativeMaterial factory sourceFrame cfg language) =
 Finsupp.single (nativeInput factory sourceFrame cfg language).expression (1 : ℤ) -
 Finsupp.single (.const (nativeValue factory sourceFrame cfg language)) 1 := by
 rw [F.source_boundary]
 have endpoint := selected_endpoint factory sourceFrame cfg language
 change Finsupp.single _ 1 - Finsupp.single (selected factory sourceFrame cfg language).event.state.1 1 = _
 rw [endpoint]
 rw [paid_raw]

theorem new_environment_sound : evaluation (R := ℤ)
 (nativeInput factory sourceFrame cfg language).environment
 (F.boundary (nativeMaterial factory sourceFrame cfg language)) = 0 :=
 (nativeMaterial factory sourceFrame cfg language).state.2.relation_old (R := ℤ)

def affineCertificate := normalizationCertificate (R := ℤ) (N.input (sourceMaterial sourceFrame cfg)).environment
 (F.boundary (sourceMaterial sourceFrame cfg))
theorem affine_correction : relationMap (R := ℤ) (N.input (sourceMaterial sourceFrame cfg)).environment
    (affineCertificate sourceFrame cfg) = F.boundary (sourceMaterial sourceFrame cfg) -
      constantMap (R := ℤ) (valueMap (R := ℤ) (N.input (sourceMaterial sourceFrame cfg)).environment
        (F.boundary (sourceMaterial sourceFrame cfg))) := source_reduction _ _

theorem actual_new_relation_in_born : F.boundary (nativeMaterial factory sourceFrame cfg language) ∈
    (bornHistory (selected factory sourceFrame cfg language) (AS.firstBase factory sourceFrame cfg language)).relationClosure :=
 new_relation_in_born _ _
theorem actual_new_faces : type_of% (new_relation_face (selected factory sourceFrame cfg language)) := new_relation_face _
theorem actual_new_full_trace : type_of% (new_full_trace (selected factory sourceFrame cfg language)) := new_full_trace _
theorem actual_native_activation : type_of% (AS.first_native_full factory sourceFrame cfg language
    (receipt factory sourceFrame cfg language).1 (Nat.le_refl _)) := AS.first_native_full factory sourceFrame cfg language (receipt factory sourceFrame cfg language).1 (Nat.le_refl _)
theorem actual_born_activation : type_of% (AS.first_born_full factory sourceFrame cfg language) := AS.first_born_full _ _ _ _

end ActualReceipt
end ActualNativeRelationTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
