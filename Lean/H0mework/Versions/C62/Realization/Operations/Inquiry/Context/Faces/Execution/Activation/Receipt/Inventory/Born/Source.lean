import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Shared
end A
abbrev target := (SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target
def outcome := (target frame configuration).targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
 ((target frame configuration).oldProjection ((installed frame configuration).embed PUnit.unit))
 ((target frame configuration).targetRoot.emitted (target frame configuration).targetInitialVisit.current)
abbrev Stock := type_of% (completeMaterial (A.epoch frame) configuration (A.Shared.actualOccurrence frame))
abbrev sourceFibre := (stockLaw (A.epoch frame) configuration).outcomeAt PUnit.unit (A.Shared.actualOccurrence frame)
def typedOutcome : type_of% (sourceFibre frame configuration) :=
 cast (type_eq_of_heq (born_complete_inventory frame configuration)) (outcome frame configuration)
theorem typed_outcome : typedOutcome frame configuration=
 Sum.inl (β:=PEmpty.{u+1}) (⟨PUnit.unit,completeMaterial (A.epoch frame) configuration
  (A.Shared.actualOccurrence frame)⟩ : Sigma fun active =>
   (stockLaw (A.epoch frame) configuration).PayloadAt PUnit.unit (A.Shared.actualOccurrence frame) active) :=
 eq_of_heq ((cast_heq_iff_heq _ _ _).mpr (born_complete_inventory frame configuration))
def stock : Stock frame configuration :=
 match typedOutcome frame configuration with
 | .inl actual => actual.2
 | .inr absent => PEmpty.elim absent
theorem stock_source : stock frame configuration=completeMaterial (A.epoch frame) configuration
 (A.Shared.actualOccurrence frame) := by
 unfold stock
 rw [typed_outcome]
abbrev physicalInventory := (stock frame configuration).1.2.1
abbrev physicalRaw := (stock frame configuration).1.2.2.1
abbrev lowRaw := (stock frame configuration).1.2.2.2.2.1
abbrev binding := (stock frame configuration).1.2.2.2.2.2.2.1
abbrev lowInventory := (stock frame configuration).2.2
def migratedEvent : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar slot) →
 PresentedRelationEventAt (Expr (PairValue PhysicalValue) configuration.LowVar slot)
 | .generator expression => .generator (expression.subst (binding frame configuration))
 | .relation word => .relation (substitution (R:=ℤ) (binding frame configuration) word)
def inventory := SourceHistoryCommon.seed
 ((physicalInventory frame configuration).map (migratedEvent frame configuration))
 (lowInventory frame configuration)
abbrev bornFrame := {SourceGeneratedInquiryReceiptAction.bornFrame frame (programme configuration) with
 inventory:=some (inventory frame configuration)}
abbrev seed := RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (bornFrame frame configuration).registered.input.expression)
abbrev consumer := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.configuration
 (seed frame configuration)
abbrev query := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
 (bornFrame frame configuration) (consumer frame configuration)
abbrev generated := SourceGeneratedInquiryReceiptAction.actualGenerated (bornFrame frame configuration) (consumer frame configuration)
end SourceGeneratedInquiryReceiptAction.Inventory.Born
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
