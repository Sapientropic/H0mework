import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source
import H0mework.Realization.Operations.InventoryLift.Substitution
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalSourceAction"

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative nativeAfterAdmission_grade receiver nextSeed nextBase scalar pair stockCfg generatedPairStock write localNativeReceipt localPaidAt)
end AS
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock (carried_scalar pair cast_mem cast_some)
end Stock
end L
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve liftEvent pairPrior mapped_trace)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions (packetAt packetAt_successor packetAt_successor_grade)
end D
namespace S
 export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next nextBorn actualOccurrence actualVisit)
end S
namespace AN
export ActualNativeRelationTransport (paid bornStock born_stock paid_in_born new_relation_in_born)
end AN
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeAt nativeEventValue)
end WB
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)

/-- The original receiver before the original language transport. -/
def nativePacket (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 AS.AdmissionPacket (W := W) (X := packet.2.2.1.LowVar) (s := s) :=
 ⟨packet.1+1,⟨AS.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
  AS.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
  AS.nextBase factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,⟨rfl⟩⟩

def packetTransport {Y Z : Sorts → Type u} (same : Y = Z) :
 AS.AdmissionPacket (W := W) (X := Y) (s := s) → AS.AdmissionPacket (W := W) (X := Z) (s := s) := by
 cases same
 exact id

theorem native_packet_actual (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 AS.nativeAfterAdmission factory packet = packetTransport packet.2.2.2.down (nativePacket factory packet) := rfl

theorem born_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : AS.AdmissionPacket (W := W) (X := Y) (s := s)) :
 AS.bornAfterNative (packetTransport same packet) = packetTransport same (AS.bornAfterNative packet) := by
 cases same
 rfl

abbrev receipt (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) := AS.localNativeReceipt (nativePacket factory packet)
def nativeValue (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) : PairValue (L.Value W packet.1) s :=
 (receipt factory packet).2.1.1
abbrev selected (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 S.frames (nativePacket factory packet).2.1.1 (AS.stockCfg (nativePacket factory packet).2.2.1)
  (0+(receipt factory packet).1)
abbrev sourceBorn (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) := AS.bornAfterNative (nativePacket factory packet)
abbrev bornStock (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 AN.bornStock (selected factory packet) (nativePacket factory packet).2.2.1
abbrev bornPairStock (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 T.preserve (selected factory packet).pairInventory
  (T.preserve ((nativePacket factory packet).2.2.1.nextPairInventory (selected factory packet))
   (AS.generatedPairStock (selected factory packet)))

/-- The actual AST retains the original actionReader material, paid trace and owner. -/
theorem receiver_input (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 HEq (nativePacket factory packet).2.1.1.registered.input
  (N.input (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1)) := HEq.rfl

theorem receiver_ast (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (nativePacket factory packet).2.1.1.registered.input.expression =
 N.expression (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1) := rfl

theorem born_ast (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (sourceBorn factory packet).2.1.1.registered.input.expression =
 (selected factory packet).request.input.expression := rfl

private theorem next_paid {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 (frame : A.M.Frame (Value := Value) (Var := Var) (sort := s))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state)
 (actual : frame.action = .inr paid) : S.next frame base = frame.mathNext := by
 unfold S.next
 rw [actual]

/-- Each paid prefix frame keeps the entire receiver inventory. -/
theorem paid_prefix_stocks (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (offset : Nat) (within : offset ≤ (receipt factory packet).1) :
 (S.frames (nativePacket factory packet).2.1.1 (AS.stockCfg (nativePacket factory packet).2.2.1) (0+offset)).inventory =
 some (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) ∧
 (S.frames (nativePacket factory packet).2.1.1 (AS.stockCfg (nativePacket factory packet).2.2.1) (0+offset)).pairInventory =
 some (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) := by
 induction offset with
 | zero => exact ⟨rfl,rfl⟩
 | succ offset previous =>
  have prior := previous (Nat.le_trans (Nat.le_succ offset) within)
  let paid := AS.localPaidAt (nativePacket factory packet)
   ⟨offset,Nat.lt_of_lt_of_le (Nat.lt_succ_self offset) within⟩
  have next : S.frames (nativePacket factory packet).2.1.1 (AS.stockCfg (nativePacket factory packet).2.2.1) (0+(offset+1)) =
    (S.frames (nativePacket factory packet).2.1.1 (AS.stockCfg (nativePacket factory packet).2.2.1) (0+offset)).mathNext := by
   change S.next _ _ = _
   exact next_paid _ _ paid.1 paid.2.down
  exact ⟨(congrArg (fun frame => frame.inventory) next).trans prior.1,
   (congrArg (fun frame => frame.pairInventory) next).trans prior.2⟩

theorem born_inventory (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (sourceBorn factory packet).2.1.1.inventory = some (bornStock factory packet) := AN.born_stock _ _

theorem born_pair_inventory (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (sourceBorn factory packet).2.1.1.pairInventory = some (bornPairStock factory packet) := rfl

private theorem preserve_generated {α : Type u} (prior : Option (RootedAccountedUnfolding α))
 (generated : RootedAccountedUnfolding α) (event : α) (present : event ∈ generated.trace) :
 event ∈ (T.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some carried => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

/-- The old event's entire literal generator or relation word is lifted. -/
def sourceLiftEvent (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (event : PresentedRelationEventAt (Expr (L.Value W packet.1) X s)) :
 PresentedRelationEventAt (Expr (L.Value W (packet.1+1)) packet.2.2.1.LowVar s) :=
 by
  letI : ∀ target,AddCommGroup (L.Value W packet.1 target) := L.groups W packet.1
  exact packet.2.2.2.down.symm ▸ T.liftEvent (W := L.Value W packet.1) (X := X) (s := s) event

theorem old_event_in_receiver (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value W packet.1) X s)))
 (present : packet.2.1.1.inventory = some prior)
 (event : PresentedRelationEventAt (Expr (L.Value W packet.1) X s)) (belongs : event ∈ prior.trace) :
 sourceLiftEvent packet event ∈ (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).trace :=
 preserve_generated _ _ _ (L.Stock.carried_scalar packet.2.1.1 packet.2.2.1 packet.2.2.2.down prior present event belongs)

theorem old_event_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value W packet.1) X s)))
 (present : packet.2.1.1.inventory = some prior)
 (event : PresentedRelationEventAt (Expr (L.Value W packet.1) X s)) (belongs : event ∈ prior.trace) :
 sourceLiftEvent packet event ∈ (bornStock factory packet).trace := by
 change sourceLiftEvent packet event ∈ (T.preserve (selected factory packet).inventory _).trace
 rw [(paid_prefix_stocks factory packet _ (Nat.le_refl _)).1]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ (old_event_in_receiver factory packet prior present event belongs)

/-- The same stopping frame's full paid trace enters the same born inventory. -/
theorem whole_paid_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (event) (present : event ∈ (SourceOperationPaidRelations.exposure (AN.paid (selected factory packet)).state.2).trace) :
 event ∈ (bornStock factory packet).trace := AN.paid_in_born _ _ event present

def sourceLiftPairEvent (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (event : PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X s)) :
 PresentedRelationEventAt (Expr (PairValue (L.Value W (packet.1+1))) packet.2.2.1.LowVar s) :=
 by
  letI : ∀ target,AddCommGroup (L.Value W packet.1 target) := L.groups W packet.1
  exact packet.2.2.2.down.symm ▸ T.liftEvent (W := PairValue (L.Value W packet.1)) (X := X) (s := s) event

theorem old_pair_event_in_receiver (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X s)))
 (present : packet.2.1.1.pairInventory = some prior)
 (event : PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X s)) (belongs : event ∈ prior.trace) :
 sourceLiftPairEvent packet event ∈ (AS.pair factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).trace := by
 have lifted : T.liftEvent event ∈ (prior.map T.liftEvent).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem belongs
 have carried := (L.Stock.cast_mem packet.2.2.2.down.symm _ _).mpr lifted
 have lower : sourceLiftPairEvent packet event ∈
   (L.Stock.pair packet.2.1.1 packet.2.2.1 packet.2.2.2.down).trace := by
  unfold L.Stock.pair T.pairPrior
  rw [present]
  change sourceLiftPairEvent packet event ∈
   (T.preserve (packet.2.2.2.down.symm ▸ some (prior.map T.liftEvent)) _).trace
  rw [L.Stock.cast_some]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 _ carried
 exact preserve_generated _ _ _ lower

theorem old_pair_event_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X s)))
 (present : packet.2.1.1.pairInventory = some prior)
 (event : PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X s)) (belongs : event ∈ prior.trace) :
 sourceLiftPairEvent packet event ∈ (bornPairStock factory packet).trace := by
 change sourceLiftPairEvent packet event ∈ (T.preserve (selected factory packet).pairInventory _).trace
 rw [(paid_prefix_stocks factory packet _ (Nat.le_refl _)).2]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ (old_pair_event_in_receiver factory packet prior present event belongs)

theorem generated_joint_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (event) (present : event ∈ (AS.generatedPairStock (selected factory packet)).trace) :
 event ∈ (bornPairStock factory packet).trace := preserve_generated _ _ _ (preserve_generated _ _ _ present)

/-- The original decoder uses the original old paid value and this native occurrence. -/
theorem decoder_source (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 ((AS.stockCfg (nativePacket factory packet).2.2.1).datum (selected factory packet)).nextEnvironmentReadAt =
 some (fun {_sourceCurrent} supplied _queryPaid =>
  AS.write factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
   (WB.oldPaid packet.2.1.1 packet.2.2.1 + WB.nativeAt packet.2.2.1 (selected factory packet) supplied)) := rfl

theorem born_environment (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (sourceBorn factory packet).2.1.1.activeEnvironment =
 AS.write factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
 (WB.oldPaid packet.2.1.1 packet.2.2.1 + nativeValue factory packet) := by
 change AS.write factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
  (WB.oldPaid packet.2.1.1 packet.2.2.1 +
   (show PairValue (L.Value W packet.1) s from WB.nativeEventValue (S.actualVisit (selected factory packet)).current.2)) = _
 have eventEq : (S.actualVisit (selected factory packet)).current.2 = (selected factory packet).event := rfl
 have same := congrArg WB.nativeEventValue eventEq
 have actual : WB.nativeEventValue (selected factory packet).event = nativeValue factory packet := by
  unfold WB.nativeEventValue
  have chosen := (receipt factory packet).2.2.2
  dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action] at chosen
  rw [chosen]
  rfl
 exact congrArg (fun value => AS.write factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
  (WB.oldPaid packet.2.1.1 packet.2.2.1 + value)) (same.trans actual)

def wordTransport {Value : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 {Y Z : Sorts → Type u} (same : Y = Z) : Formal ℤ Value Y s ≃ₗ[ℤ] Formal ℤ Value Z s := by
 cases same
 exact LinearEquiv.refl ℤ _

private theorem relation_transport {Value : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 {Y Z : Sorts → Type u} (same : Y = Z) (word : Formal ℤ Value Y s) :
 (same ▸ (PresentedRelationEventAt.relation word : PresentedRelationEventAt (Expr Value Y s))) =
 PresentedRelationEventAt.relation (wordTransport same word) := by cases same; rfl

/-- Linear extension of the original literal lift, in the original receiver language. -/
def sourceWordAction (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 Formal ℤ (L.Value W packet.1) X s →ₗ[ℤ] Formal ℤ (L.Value W (packet.1+1)) packet.2.2.1.LowVar s := by
 letI : ∀ target,AddCommGroup (L.Value W packet.1 target) := L.groups W packet.1
 exact (wordTransport packet.2.2.2.down.symm).toLinearMap.comp (liftMap (R := ℤ))

theorem source_word_action_relation (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (word : Formal ℤ (L.Value W packet.1) X s) :
 sourceLiftEvent packet (.relation word) = .relation (sourceWordAction packet word) :=
 relation_transport packet.2.2.2.down.symm ((liftMap (R := ℤ)) word)

/-- This complete coefficient word action is consumed by the actual born inventory. -/
theorem source_word_action_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value W packet.1) X s)))
 (present : packet.2.1.1.inventory = some prior)
 (word : Formal ℤ (L.Value W packet.1) X s) (belongs : .relation word ∈ prior.trace) :
 .relation (sourceWordAction packet word) ∈ (bornStock factory packet).trace := by
 simpa only [source_word_action_relation] using old_event_in_born factory packet prior present (.relation word) belongs

def environmentTransport {Value : Sorts → Type u} {Y Z : Sorts → Type u} (same : Y = Z) :
 Env Value Y → Env Value Z := by cases same; exact id

def receiverEnvironment (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 Env (PairValue (L.Value W packet.1)) X :=
 environmentTransport (Value := PairValue (L.Value W packet.1)) packet.2.2.2.down
  (nativePacket factory packet).2.1.1.registered.input.environment

def receiverOld (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) : Env (L.Value W packet.1) X :=
 fun target name => (receiverEnvironment factory packet target name).1

def receiverIncrement (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) : Env (L.Value W packet.1) X :=
 fun target name => (receiverEnvironment factory packet target name).2

private theorem word_inventory {Value : Sorts → Type u} [∀ target,AddCommGroup (Value target)]
 {Y Z : Sorts → Type u} (same : Y = Z) (environment : Env (PairValue Value) Z) :
 (evaluation (R := ℤ) environment).comp
  ((wordTransport (s := s) same).toLinearMap.comp (liftMap (R := ℤ) (Value := Value) (Var := Y))) =
 updateInventory (R := ℤ)
  (fun target name => (environmentTransport same.symm environment target name).1)
  (fun target name => (environmentTransport same.symm environment target name).2) := by
 cases same
 exact evaluation_liftMap _ _

/-- The full word square reads its old/effect coordinates from the actual source receiver. -/
theorem source_word_action_inventory (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (evaluation (R := ℤ) (nativePacket factory packet).2.1.1.registered.input.environment).comp
  (sourceWordAction packet) =
 updateInventory (R := ℤ) (receiverOld factory packet) (receiverIncrement factory packet) :=
 word_inventory (Value := L.Value W packet.1) packet.2.2.2.down.symm
  (nativePacket factory packet).2.1.1.registered.input.environment

theorem source_word_action_substitution (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (binding : ∀ target,X target → Expr (L.Value W packet.1) X target) :
 (sourceWordAction packet).comp (substitution (R := ℤ) binding) =
 (wordTransport packet.2.2.2.down.symm).toLinearMap.comp
  ((substitution (R := ℤ) (fun target name => liftExpr (binding target name))).comp (liftMap (R := ℤ))) := by
 change (wordTransport packet.2.2.2.down.symm).toLinearMap.comp
  ((liftMap (R := ℤ) (Value := L.Value W packet.1) (Var := X)).comp (substitution (R := ℤ) binding)) = _
 exact congrArg (fun action => (wordTransport packet.2.2.2.down.symm).toLinearMap.comp action)
  (SubstitutionLift.word (R := ℤ) (V := L.Value W packet.1) (X := X) (Y := X) binding)

variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

/-- All source AST and inventory statements above belong to this original next packet. -/
theorem actual_next_packet (ordinal : Nat) :
 D.packetAt factory initial cfg language (ordinal+1) =
 packetTransport (D.packetAt factory initial cfg language ordinal).2.2.2.down
  (sourceBorn factory (D.packetAt factory initial cfg language ordinal)) :=
 (D.packetAt_successor factory initial cfg language ordinal).trans
  ((congrArg AS.bornAfterNative (native_packet_actual factory _)).trans (born_transport _ _))

end ActualCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
