import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Consumer

import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalResidualModelSplice"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalRootResidualConsumer"

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalResidualModelSplice
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace CA
export ActualCofinalCommonAction (site siteAction action actions projection model_fibre action_source_word)
end CA
namespace T
export ActualCofinalNativeTower (NativeValue Words CommonWords component stageInventory nativeInventory)
export ActualCofinalNativeTower.SF (Factory)
export ActualCofinalNativeTower.L (Value groups)
export ActualCofinalNativeTower.M (Frame)
export ActualCofinalNativeTower.A (Programme)
end T
namespace A
export ActualCofinalCommonAction.A (AdmissionPacket sourceWordAction sourceBorn packetTransport actual_next_packet wordTransport)
end A

section Universal
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)] {s : Sorts}

/-- Relations vanishing in every environment, before selecting any native observer. -/
def semanticZero : Submodule ℤ (Formal ℤ Value Var s) where
 carrier := fun word => ∀ environment : Env Value Var, evaluation environment word = 0
 zero_mem' := by intro environment; exact map_zero _
 add_mem' := by intro left right hleft hright environment; rw [map_add,hleft environment,hright environment,zero_add]
 smul_mem' := by intro coefficient word member environment; rw [map_smul,member environment,smul_zero]

theorem universal_inventory_zero (word : Formal ℤ Value Var s)
 (member : word ∈ semanticZero) (old increment : Env Value Var) :
 updateInventory old increment word = 0 := by
 have equation := LinearMap.congr_fun (evaluation_update old increment) word
 have effect : effectEvaluator old increment word = 0 := by
  rw [LinearMap.add_apply,member (old+increment),member old,zero_add] at equation
  exact equation.symm
 exact Prod.ext (member old) effect

theorem lift_semantic_zero (word : Formal ℤ Value Var s) (member : word ∈ semanticZero) :
 liftMap word ∈ semanticZero (Value := PairValue Value) := by
 intro environment
 let old : Env Value Var := fun target name => (environment target name).1
 let increment : Env Value Var := fun target name => (environment target name).2
 have same : pairEnvironment old increment = environment := by
  funext target name
  exact Prod.eta _
 rw [←same]
 change (evaluation (pairEnvironment old increment)).comp liftMap word = 0
 rw [evaluation_liftMap]
 exact universal_inventory_zero word member old increment

theorem language_semantic_zero {Y Z : Sorts → Type u} (same : Y = Z)
 (word : Formal ℤ Value Y s) (member : word ∈ semanticZero) :
 A.wordTransport same word ∈ semanticZero (Var := Z) := by
 cases same
 exact member

theorem residual_semantic_zero (raw prior : Expr Value Var s) :
 Finsupp.single (.add raw (.linear (-AddMonoidHom.id (Value s)) prior)) 1 -
 (Finsupp.single raw 1 - Finsupp.single prior 1) ∈ semanticZero := by
 intro environment
 rw [map_sub,map_sub]
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,
  Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply]
 abel
end Universal

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target

abbrev PacketWords (packet : A.AdmissionPacket (W := W) (X := X) (s := s)) :=
 Formal ℤ (T.Value W packet.1) X s

/-- Generic dependent equality elimination for the original full packet. -/
def packetWordTransport {first second : A.AdmissionPacket (W := W) (X := X) (s := s)}
 (same : first = second) : PacketWords first ≃ₗ[ℤ] PacketWords second := by
 cases same
 exact LinearEquiv.refl ℤ _

def packetLanguageWord {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s)) :
 Formal ℤ (T.Value W packet.1) Y s ≃ₗ[ℤ]
 Formal ℤ (T.Value W (A.packetTransport same packet).1) Z s := by
 cases same
 exact LinearEquiv.refl ℤ _

theorem packet_semantic_zero {first second : A.AdmissionPacket (W := W) (X := X) (s := s)}
 (same : first = second) (word : PacketWords first) (member : word ∈ semanticZero) :
 packetWordTransport same word ∈ semanticZero := by
 cases same
 exact member

theorem packet_language_semantic_zero {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : A.AdmissionPacket (W := W) (X := Y) (s := s))
 (word : Formal ℤ (T.Value W packet.1) Y s) (member : word ∈ semanticZero) :
 packetLanguageWord same packet word ∈ semanticZero := by
 cases same
 exact member

theorem source_action_semantic_zero (packet : A.AdmissionPacket (W := W) (X := X) (s := s))
 (word : PacketWords packet) (member : word ∈ semanticZero) :
 A.sourceWordAction packet word ∈ semanticZero := by
 change A.wordTransport packet.2.2.2.down.symm (liftMap word) ∈ semanticZero
 exact language_semantic_zero packet.2.2.2.down.symm (liftMap word) (lift_semantic_zero word member)

variable (factory : T.Factory W X s)
variable (initial : T.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : T.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

theorem site_action_semantic_zero (ordinal : Nat)
 (word : T.Words factory initial cfg language ordinal) (member : word ∈ semanticZero) :
 CA.siteAction factory initial cfg language ordinal word ∈ semanticZero := by
 change packetWordTransport (A.actual_next_packet factory initial cfg language ordinal).symm
  (packetLanguageWord (CA.site factory initial cfg language ordinal).2.2.2.down
   (A.sourceBorn factory (CA.site factory initial cfg language ordinal))
   (A.sourceWordAction (CA.site factory initial cfg language ordinal) word)) ∈ semanticZero
 exact packet_semantic_zero _ _
  (packet_language_semantic_zero _ _ _ (source_action_semantic_zero _ word member))

theorem all_word_site_invisible (ordinal : Nat)
 (word : T.Words factory initial cfg language ordinal) (member : word ∈ semanticZero)
 (history : List PUnit.{u+1}) (target : Nat) :
 T.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (CA.actions factory initial cfg language) history
   (DFinsupp.single ordinal word)) = 0 := by
 induction history generalizing ordinal word with
 | nil =>
  change T.nativeInventory factory initial cfg language target
   ((DFinsupp.single ordinal word) target) = 0
  by_cases same : ordinal = target
  · subst target
    rw [DFinsupp.single_eq_same]
    exact universal_inventory_zero word member _ _
  · rw [DFinsupp.single_eq_of_ne (Ne.symm same)]
    exact map_zero _
 | cons letter rest previous =>
  change T.stageInventory factory initial cfg language target
   (SourceGeneratedActionWords.run (CA.actions factory initial cfg language) rest
    (CA.action factory initial cfg language (DFinsupp.single ordinal word))) = 0
  rw [CA.action_source_word]
  exact previous (ordinal+1) (CA.siteAction factory initial cfg language ordinal word)
   (site_action_semantic_zero factory initial cfg language ordinal word member)

/-- The actual Model recognizes any universally generated local semantic relation. -/
theorem semantic_model_equiv (ordinal : Nat)
 (left right : T.Words factory initial cfg language ordinal)
 (member : left - right ∈ semanticZero) :
 CA.projection factory initial cfg language (DFinsupp.single ordinal left) =
 CA.projection factory initial cfg language (DFinsupp.single ordinal right) := by
 apply (CA.model_fibre factory initial cfg language _ _).mpr
 intro history target
 apply sub_eq_zero.mp
 rw [←map_sub,←map_sub,←DFinsupp.single_sub]
 exact all_word_site_invisible factory initial cfg language ordinal _ member history target

/-- Every allowed action word and every native site recognize the executable residual and paid boundary. -/
theorem residual_boundary_model (ordinal : Nat)
 (raw prior : Expr (T.NativeValue factory initial cfg language ordinal) X s) :
 CA.projection factory initial cfg language
  (DFinsupp.single ordinal (Finsupp.single
   (.add raw (.linear (-AddMonoidHom.id (T.NativeValue factory initial cfg language ordinal s)) prior)) 1)) =
 CA.projection factory initial cfg language
  (DFinsupp.single ordinal (Finsupp.single raw 1 - Finsupp.single prior 1)) :=
 semantic_model_equiv factory initial cfg language ordinal _ _ (residual_semantic_zero raw prior)

/-- The original material's residual expression is recognized against its full paid boundary. -/
theorem actual_residual_boundary_model (ordinal : Nat) :
 CA.projection factory initial cfg language (ActualCofinalNativeTower.residualWord factory initial cfg language ordinal) =
 CA.projection factory initial cfg language
  (DFinsupp.single ordinal
   (Finsupp.single (ActualCofinalNativeTower.C.materialAtStop factory initial cfg language ordinal).raw 1 -
    Finsupp.single (ActualCofinalNativeTower.C.materialAtStop factory initial cfg language ordinal).state.1 1)) :=
 residual_boundary_model factory initial cfg language ordinal _ _

end ActualCofinalResidualModelSplice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
