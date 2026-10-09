import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.Consumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : A.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
abbrev site (ordinal : Nat) := D.packetAt factory initial cfg language ordinal

/-- Every component is read from the same original source action and original next packet. -/
theorem actual_next_inventory (ordinal : Nat) :
 type_of% (actual_next_packet factory initial cfg language ordinal) ∧
 type_of% (receiver_input factory (site factory initial cfg language ordinal)) ∧
 type_of% (receiver_ast factory (site factory initial cfg language ordinal)) ∧
 type_of% (born_ast factory (site factory initial cfg language ordinal)) ∧
 (∀ offset,type_of% (paid_prefix_stocks factory (site factory initial cfg language ordinal) offset)) ∧
 type_of% (born_inventory factory (site factory initial cfg language ordinal)) ∧
 type_of% (born_pair_inventory factory (site factory initial cfg language ordinal)) ∧
 type_of% (old_event_in_born factory (site factory initial cfg language ordinal)) ∧
 type_of% (old_pair_event_in_born factory (site factory initial cfg language ordinal)) ∧
 type_of% (whole_paid_in_born factory (site factory initial cfg language ordinal)) ∧
 type_of% (generated_joint_in_born factory (site factory initial cfg language ordinal)) ∧
 type_of% (decoder_source factory (site factory initial cfg language ordinal)) ∧
 type_of% (born_environment factory (site factory initial cfg language ordinal)) :=
 ⟨actual_next_packet factory initial cfg language ordinal,
  receiver_input factory _,receiver_ast factory _,born_ast factory _,
  fun offset within => paid_prefix_stocks factory _ offset within,
  born_inventory factory _,born_pair_inventory factory _,
  old_event_in_born factory _,old_pair_event_in_born factory _,
  whole_paid_in_born factory _,generated_joint_in_born factory _,
  decoder_source factory _,born_environment factory _⟩

/-- Complete coefficient words act on the actual born inventory and exact decoder. -/
theorem actual_next_word (ordinal : Nat)
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (L.Value W (site factory initial cfg language ordinal).1) X s)))
 (present : (site factory initial cfg language ordinal).2.1.1.inventory = some prior)
 (word : Formal ℤ (L.Value W (site factory initial cfg language ordinal).1) X s)
 (belongs : .relation word ∈ prior.trace) :
 type_of% (actual_next_packet factory initial cfg language ordinal) ∧
 type_of% (born_inventory factory (site factory initial cfg language ordinal)) ∧
 .relation (sourceWordAction (site factory initial cfg language ordinal) word) ∈
  (bornStock factory (site factory initial cfg language ordinal)).trace ∧
 type_of% (source_word_action_inventory factory (site factory initial cfg language ordinal)) ∧
 type_of% (born_environment factory (site factory initial cfg language ordinal)) :=
 ⟨actual_next_packet factory initial cfg language ordinal,born_inventory factory _,
  source_word_action_in_born factory _ prior present word belongs,
  source_word_action_inventory factory _,born_environment factory _⟩

/-- Syntax substitution acts before this same source-generated word action. -/
theorem actual_next_substitution (ordinal : Nat)
 (binding : ∀ target,X target → Expr (L.Value W (site factory initial cfg language ordinal).1) X target) :
 type_of% (actual_next_packet factory initial cfg language ordinal) ∧
 type_of% (source_word_action_substitution (site factory initial cfg language ordinal) binding) :=
 ⟨actual_next_packet factory initial cfg language ordinal,source_word_action_substitution _ binding⟩

end ActualCofinalSourceAction.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
