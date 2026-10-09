import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP120CommonSourceActionControls
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open ActualCofinalCommonAction
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance nativeGroups (grade : Nat) (target : Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target
variable (factory : T.Factory W X s)
variable (initial : T.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : T.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
example (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 type_of% (action_source_word factory initial cfg language ordinal word) := action_source_word factory initial cfg language ordinal word
example (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 type_of% (action_next_component factory initial cfg language ordinal word) := action_next_component factory initial cfg language ordinal word
example (ordinal : Nat) (word : T.Words factory initial cfg language ordinal)
 (member : WordInInventory (site factory initial cfg language ordinal) word) :
 type_of% (site_action_inventory factory initial cfg language ordinal word member) := site_action_inventory factory initial cfg language ordinal word member
example (ordinal : Nat) (word : T.Words factory initial cfg language ordinal) :
 type_of% (actual_receiver_square factory initial cfg language ordinal word) := actual_receiver_square factory initial cfg language ordinal word
example (word : T.CommonWords factory initial cfg language) :
 type_of% (model_action_source factory initial cfg language word) := model_action_source factory initial cfg language word
example (left right : T.CommonWords factory initial cfg language) :
 type_of% (model_fibre factory initial cfg language left right) := model_fibre factory initial cfg language left right
example (word : T.CommonWords factory initial cfg language) :
 type_of% (native_restriction_source factory initial cfg language word) := native_restriction_source factory initial cfg language word
example (word : T.CommonWords factory initial cfg language) :
 type_of% (model_action_native factory initial cfg language word) := model_action_native factory initial cfg language word
example (ordinal : Nat) (word : T.Words factory initial cfg language ordinal)
 (member : WordInInventory (site factory initial cfg language ordinal) word) :
 type_of% (actual_source_word_step factory initial cfg language ordinal word member) := actual_source_word_step factory initial cfg language ordinal word member
example (history : List PUnit.{u+1}) (word : T.CommonWords factory initial cfg language) (ordinal : Nat) :
 type_of% (model_read_source factory initial cfg language history word ordinal) := model_read_source factory initial cfg language history word ordinal
example (history : List PUnit.{u+1}) (value : Model factory initial cfg language) (ordinal : Nat) :
 type_of% (model_read_action factory initial cfg language history value ordinal) := model_read_action factory initial cfg language history value ordinal
example {Result : Sort v} (ordinal : Nat) (word : T.Words factory initial cfg language ordinal)
 (member : WordInInventory (site factory initial cfg language ordinal) word)
 (consume : WordInInventory (site factory initial cfg language (ordinal+1))
   (siteAction factory initial cfg language ordinal word) →
  type_of% (actual_source_word_step factory initial cfg language ordinal word member) → Result) : Result :=
 consume (site_action_inventory factory initial cfg language ordinal word member)
  (actual_source_word_step factory initial cfg language ordinal word member)
#print axioms siteAction
#print axioms action
#print axioms action_source_word
#print axioms action_next_component
#print axioms site_action_inventory
#print axioms actual_receiver_square
#print axioms Model
#print axioms modelAction
#print axioms model_action_source
#print axioms model_fibre
#print axioms nativeRestriction
#print axioms native_restriction_source
#print axioms model_action_native
#print axioms actual_source_word_step
#print axioms model_read_source
#print axioms model_read_action
end CP120CommonSourceActionControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
