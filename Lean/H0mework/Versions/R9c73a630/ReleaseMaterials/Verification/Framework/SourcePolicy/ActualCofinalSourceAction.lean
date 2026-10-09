import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP119ActualSourceActionControls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open ActualCofinalSourceAction
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance nativeGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
example : type_of% (native_packet_actual factory packet) := native_packet_actual factory packet
example : type_of% (receiver_input factory packet) := receiver_input factory packet
example : type_of% (receiver_ast factory packet) := receiver_ast factory packet
example : type_of% (born_ast factory packet) := born_ast factory packet
example (offset : Nat) : type_of% (paid_prefix_stocks factory packet offset) := paid_prefix_stocks factory packet offset
example : type_of% (born_inventory factory packet) := born_inventory factory packet
example : type_of% (born_pair_inventory factory packet) := born_pair_inventory factory packet
example : type_of% (whole_paid_in_born factory packet) := whole_paid_in_born factory packet
example : type_of% (generated_joint_in_born factory packet) := generated_joint_in_born factory packet
example : type_of% (decoder_source factory packet) := decoder_source factory packet
example : type_of% (born_environment factory packet) := born_environment factory packet
example (word : Formal ℤ (L.Value W packet.1) X s) : type_of% (source_word_action_relation packet word) :=
 source_word_action_relation packet word
example : type_of% (source_word_action_inventory factory packet) := source_word_action_inventory factory packet
example (binding : ∀ target,X target → Expr (L.Value W packet.1) X target) :
 type_of% (source_word_action_substitution packet binding) := source_word_action_substitution packet binding
example (ordinal : Nat) : type_of% (ActualCofinalSourceAction.Consumer.actual_next_inventory factory initial cfg language ordinal) :=
 ActualCofinalSourceAction.Consumer.actual_next_inventory factory initial cfg language ordinal
example (ordinal : Nat)
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (L.Value W (D.packetAt factory initial cfg language ordinal).1) X s)))
 (present : (D.packetAt factory initial cfg language ordinal).2.1.1.inventory = some prior)
 (word : Formal ℤ (L.Value W (D.packetAt factory initial cfg language ordinal).1) X s)
 (belongs : .relation word ∈ prior.trace) :
 type_of% (ActualCofinalSourceAction.Consumer.actual_next_word factory initial cfg language ordinal prior present word belongs) :=
 ActualCofinalSourceAction.Consumer.actual_next_word factory initial cfg language ordinal prior present word belongs
example (ordinal : Nat)
 (binding : ∀ target,X target → Expr (L.Value W (D.packetAt factory initial cfg language ordinal).1) X target) :
 type_of% (ActualCofinalSourceAction.Consumer.actual_next_substitution factory initial cfg language ordinal binding) :=
 ActualCofinalSourceAction.Consumer.actual_next_substitution factory initial cfg language ordinal binding
example {Result : Sort v} (ordinal : Nat)
 (consume : (next : AS.AdmissionPacket (W := W) (X := X) (s := s)) →
 next = packetTransport (D.packetAt factory initial cfg language ordinal).2.2.2.down
  (sourceBorn factory (D.packetAt factory initial cfg language ordinal)) →
 type_of% (ActualCofinalSourceAction.Consumer.actual_next_inventory factory initial cfg language ordinal) → Result) : Result :=
 consume (D.packetAt factory initial cfg language (ordinal+1))
  (actual_next_packet factory initial cfg language ordinal)
  (ActualCofinalSourceAction.Consumer.actual_next_inventory factory initial cfg language ordinal)
#print axioms native_packet_actual
#print axioms receiver_input
#print axioms receiver_ast
#print axioms born_ast
#print axioms paid_prefix_stocks
#print axioms born_inventory
#print axioms born_pair_inventory
#print axioms old_event_in_born
#print axioms old_pair_event_in_born
#print axioms whole_paid_in_born
#print axioms generated_joint_in_born
#print axioms decoder_source
#print axioms born_environment
#print axioms source_word_action_relation
#print axioms source_word_action_in_born
#print axioms source_word_action_inventory
#print axioms source_word_action_substitution
#print axioms actual_next_packet
#print axioms ActualCofinalSourceAction.Consumer.actual_next_inventory
#print axioms ActualCofinalSourceAction.Consumer.actual_next_word
#print axioms ActualCofinalSourceAction.Consumer.actual_next_substitution
end CP119ActualSourceActionControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
