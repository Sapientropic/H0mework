import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Consumer
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local instance] levelGroups
open private packetTransport from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Stage
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (generatedPairStock)
end AS
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn actualVisit)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_paid_prefix)
end Prefix
end S
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression)
end N
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (target_expression)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value)
end OF
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}

namespace Generic
variable {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
variable (frame : M.Frame (Value := U) (Var := Y) (sort := s))
variable (cfg : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s))
theorem paid_expression : (R.actualMaterial frame cfg).state.1 =
 .const ((R.actionResultAt frame cfg (S.actualOccurrence frame)).2.2.1) :=
 OF.target_expression (S.baseRoot frame cfg).toAuthoritativeRoot (S.visit frame cfg).current
  (fun _ => R.actionReader frame cfg (S.actualOccurrence frame))
theorem born_expression : (S.nextBorn frame cfg).registered.input.expression =
 Expr.add frame.registered.input.expression (Expr.linear (-AddMonoidHom.id (U s)) frame.event.state.1) := rfl
theorem negate_paid (expr : Expr U Y s) (env : Env U Y) :
 (Expr.linear (-AddMonoidHom.id (U s)) (Expr.linear (-AddMonoidHom.id (U s)) expr)).eval env = expr.eval env := by
 simp only [Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, neg_neg]
theorem paid_prefix_expression (count : Nat) (within : count ≤ (S.Complete.receipt cfg frame 0).1) :
 (S.frames frame cfg (0+count)).registered.input.expression = frame.registered.input.expression := by
 induction count with
 | zero => rfl
 | succ count previous =>
  have paid := S.Prefix.receipt_paid_prefix cfg frame 0 ⟨count, by omega⟩
  have move : S.frames frame cfg (0+(count+1)) = (S.frames frame cfg (0+count)).mathNext := by
   change S.next (S.frames frame cfg (0+count)) cfg = _
   unfold S.next
   rw [paid.2.down]
  exact (congrArg (fun current : M.Frame (Value := U) (Var := Y) (sort := s) =>
   current.registered.input.expression) move).trans (previous (by omega))
end Generic

-- R-free extraction: the two residual constructors preserve the complete paid AST.
theorem after_native_retained (sourceFactory : SF.Factory W X s)
 (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 HEq
  (retainedCode (AS.bornAfterNative (AS.nativeAfterAdmission sourceFactory packet)).1
   (AS.bornAfterNative (AS.nativeAfterAdmission sourceFactory packet)).2.1.1)
  (Expr.linear (-AddMonoidHom.id (PairValue (L.Value W packet.1) s))
   (Expr.linear (-AddMonoidHom.id (PairValue (L.Value W packet.1) s))
    (R.actualMaterial packet.2.1.1 packet.2.2.1).state.1)) := by
 rcases packet with ⟨n, ⟨source, seed⟩, ⟨Y, datum, inventory, pairInventory⟩, ⟨language⟩⟩
 change Y = X at language
 cases language
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let native := AS.receiver sourceFactory n (source, seed) cfg rfl
 let base := AS.nextBase sourceFactory n (source, seed) cfg rfl
 let distance := (S.Complete.receipt (AS.stockCfg base) native 0).1
 let selected := S.frames native (AS.stockCfg base) (0+distance)
 have oldRegistered : native.registered.input.expression = N.expression (R.actualMaterial source cfg) := rfl
 have kept : selected.registered.input.expression = native.registered.input.expression :=
  Generic.paid_prefix_expression native (AS.stockCfg base) distance (Nat.le_refl _)
 have born := Generic.born_expression selected (AS.stockCfg base)
 have sourceRaw := born.trans (congrArg
  (fun expr : Expr (PairValue (L.Value W n)) X s => Expr.add expr
   (Expr.linear (-AddMonoidHom.id (PairValue (L.Value W n) s)) selected.event.state.1))
  (kept.trans oldRegistered))
 dsimp only [cfg, native, base, distance, selected] at sourceRaw
 dsimp only [AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id]
 unfold retainedCode
 rw [sourceRaw]
 rfl

def retainedValue (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 (retainedCode packet.1 packet.2.1.1).eval packet.2.1.1.registered.input.environment

theorem after_native_value (sourceFactory : SF.Factory W X s)
 (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 HEq (retainedValue (AS.bornAfterNative (AS.nativeAfterAdmission sourceFactory packet)))
  (R.actionResultAt packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1)).2.2.1 := by
 have sourceAst := after_native_retained sourceFactory packet
 rcases packet with ⟨n, ⟨source, seed⟩, ⟨Y, datum, inventory, pairInventory⟩, ⟨language⟩⟩
 change Y = X at language
 cases language
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let packet : AS.AdmissionPacket (W := W) (X := X) (s := s) := ⟨n, ⟨source, seed⟩, cfg, ⟨rfl⟩⟩
 let next := AS.bornAfterNative (AS.nativeAfterAdmission sourceFactory packet)
 let env := next.2.1.1.registered.input.environment
 dsimp only [AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id] at sourceAst
 have astEq := eq_of_heq sourceAst
 have read := congrArg (fun expr : Expr (PairValue (L.Value W n)) X s => expr.eval env) astEq
 have normal := Generic.paid_expression source cfg
 have constantRead := congrArg (fun expr : Expr (PairValue (L.Value W n)) X s => expr.eval env) normal
 have paidRead := Generic.negate_paid (R.actualMaterial source cfg).state.1 env
 dsimp only [retainedValue, AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id]
 exact heq_of_eq (read.trans (paidRead.trans constantRead))

theorem native_whole_value (baseFactory : SF.Factory W X s) (f : W s →+ W s) (n : Nat)
 (source : M.Frame (Value := L.Value W n) (Var := X) (sort := s)) (seed : SF.Seed W X s n)
 (datum : type_of% (SF.cfg (factory baseFactory f) n seed).datum)
 (inventory : type_of% (SF.cfg (factory baseFactory f) n seed).nextInventory)
 (pairInventory : type_of% (SF.cfg (factory baseFactory f) n seed).nextPairInventory)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := X) (sort := s)) :
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 (R.actionResultAt frame (AS.nextCfg (factory baseFactory f) n (source, seed) cfg rfl)
  (S.actualOccurrence frame)).2.2.1 =
 (actionAt f (n+1) ((retainedCode (n+1) frame).eval frame.registered.input.environment), 0) := by
 dsimp only
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let programme := AS.nextCfg (factory baseFactory f) n (source, seed) cfg rfl
 have sourceRaw := AS.next_action_reader (factory baseFactory f) n (source, seed) cfg rfl frame (S.actualOccurrence frame)
 have templateRaw := factory_reader baseFactory f (n+1)
  (AS.nextSeed (factory baseFactory f) n (source, seed) cfg rfl) frame
 have read := congrArg (fun input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (L.Value W (n+1))) (Var := X) (sort := s) => input.expression.eval input.environment)
  (sourceRaw.trans templateRaw)
 exact (OF.source_value (S.baseRoot frame programme).toAuthoritativeRoot (R.actionReader frame programme)
  (S.actualOccurrence frame)).trans (read.trans (raw_value f (n+1) frame))

def WholeStep (f : W s →+ W s) (packet next : AS.AdmissionPacket (W := W) (X := X) (s := s)) : Prop :=
 HEq (R.actionResultAt next.2.1.1 next.2.2.1 (S.actualOccurrence next.2.1.1)).2.2.1
  ((@pairAction (L.Value W packet.1 s) (levelGroups packet.1 s) (actionAt f packet.1))
   (R.actionResultAt packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1)).2.2.1,
   (0 : PairValue (L.Value W packet.1) s))

theorem after_native_whole_action (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 WholeStep f packet (AS.bornAfterNative (AS.nativeAfterAdmission (factory baseFactory f) packet)) := by
 unfold WholeStep
 have feed := after_native_value (factory baseFactory f) packet
 rcases packet with ⟨n, ⟨source, seed⟩, ⟨Y, datum, inventory, pairInventory⟩, ⟨language⟩⟩
 change Y = X at language
 cases language
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let packet : AS.AdmissionPacket (W := W) (X := X) (s := s) := ⟨n, ⟨source, seed⟩, cfg, ⟨rfl⟩⟩
 let next := AS.bornAfterNative (AS.nativeAfterAdmission (factory baseFactory f) packet)
 have generated := native_whole_value baseFactory f n source seed datum inventory pairInventory next.2.1.1
 have sourceFeed := congrArg (fun value : L.Value W (n+1) s =>
  (actionAt f (n+1) value, (0 : L.Value W (n+1) s))) (eq_of_heq feed)
 dsimp only [retainedValue, AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id] at sourceFeed
 dsimp only [next, packet, cfg, AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id] at generated
 dsimp only [AS.nativeAfterAdmission, AS.bornAfterNative, AS.localNativeReceipt, packetTransport, id]
 exact heq_of_eq (generated.trans sourceFeed)

namespace Generic
variable {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
variable (frame : M.Frame (Value := U) (Var := Y) (sort := s))
variable (base : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s))
def birthStock := Stock.preserve frame.pairInventory
 (Stock.preserve (base.nextPairInventory frame) (AS.generatedPairStock frame))
theorem birth_stock : (S.nextBorn frame (AS.stockCfg base)).pairInventory = some (birthStock frame base) := rfl
private theorem preserves_generated {T : Type u} (prior : Option (RootedAccountedUnfolding T))
 (generated : RootedAccountedUnfolding T) (event : T) (present : event ∈ generated.trace) :
 event ∈ (Stock.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem birth_keeps_callback
 (written : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue U) Y s)))
 (callback : base.nextPairInventory frame = some written) :
 ∀ event ∈ written.trace, event ∈ (birthStock frame base).trace := by
 intro event present
 unfold birthStock
 rw [callback]
 exact preserves_generated _ _ _ ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
end Generic

def selected (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 S.frames packet.2.1.1 (AS.stockCfg packet.2.2.1) (0+(AS.localNativeReceipt packet).1)
def writtenStock (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 Generic.birthStock (selected packet) packet.2.2.1
theorem actual_born_stock (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (AS.bornAfterNative packet).2.1.1.pairInventory = some (writtenStock packet) := rfl

theorem actual_complete_query_written (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 ∀ event ∈ (completeQueryWritten (AS.nativeAfterAdmission (factory baseFactory f) packet).1
  (selected (AS.nativeAfterAdmission (factory baseFactory f) packet))).trace,
 event ∈ (writtenStock (AS.nativeAfterAdmission (factory baseFactory f) packet)).trace := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, inventory, pairInventory⟩, ⟨language⟩⟩
 change Y = X at language
 cases language
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let nextSeed := AS.nextSeed (factory baseFactory f) n (frame, seed) cfg rfl
 let native : AS.AdmissionPacket (W := W) (X := X) (s := s) :=
  ⟨n+1, ⟨AS.receiver (factory baseFactory f) n (frame, seed) cfg rfl, nextSeed⟩,
   AS.nextBase (factory baseFactory f) n (frame, seed) cfg rfl, ⟨rfl⟩⟩
 have callback : native.2.2.1.nextPairInventory (selected native) =
  some (completePairOutput baseFactory (n+1) nextSeed (selected native)) := rfl
 have carried := Generic.birth_keeps_callback (selected native) native.2.2.1
  (completePairOutput baseFactory (n+1) nextSeed (selected native)) callback
 intro event present
 dsimp only [AS.nativeAfterAdmission, packetTransport, id, writtenStock] at present ⊢
 exact carried event (completePairOutput_query baseFactory (n+1) nextSeed (selected native) event present)

-- Faces and duality consume the selected source occurrence of THIS native packet.
def actual_native_faces (baseFactory : SF.Factory W X s) (f : W s →+ W s)
 (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 let native := AS.nativeAfterAdmission (factory baseFactory f) packet
 InstalledFaces (selected native) (methodBase baseFactory f native.1 native.2.1.2)
  (AS.stockCfg native.2.2.1) := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, inventory, pairInventory⟩, ⟨language⟩⟩
 change Y = X at language
 cases language
 let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
  ⟨X, datum, inventory, pairInventory⟩
 let packet : AS.AdmissionPacket (W := W) (X := X) (s := s) := ⟨n, ⟨frame, seed⟩, cfg, ⟨rfl⟩⟩
 exact templateFourFaces baseFactory f n (frame, seed) cfg rfl
  (selected (AS.nativeAfterAdmission (factory baseFactory f) packet))

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
