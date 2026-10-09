import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Laws
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
import H0mework.Realization.Operations.Execution.Substitution.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
def stockLaw : SourceNativeProjectionLaw
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} supplied _ => type_of% (completeMaterial frame configuration supplied)
 project := fun _ {_current} supplied _ => completeMaterial frame configuration supplied
def component : SourceNativeProjectionLaw
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
 match (configuration.datum frame).component with
 | none => stockLaw frame configuration
 | some old => ({(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base with
     projectionLaw:=old}.withProjectionCoface (stockLaw frame configuration)).projectionLaw
def programme := {configuration with
 datum := fun sourceFrame => {
  component := some (component sourceFrame configuration)
  reader := reader sourceFrame configuration
  nextEnvironmentRead := none
  nextEnvironmentReadAt := match (configuration.datum sourceFrame).nextEnvironmentReadAt with
   | some read => some (fun {_current} supplied _ => read supplied (lowResult sourceFrame configuration supplied).2.2.1)
   | none => match (configuration.datum sourceFrame).nextEnvironmentRead with
     | none => none
     | some read => some (fun {_current} supplied _ => read (lowResult sourceFrame configuration supplied).2.2.1) } }
def stockEmbedding : SourceNativeProjectionLaw.InstallationAt
 (stockLaw frame configuration) (component frame configuration) := by
 unfold component
 cases (configuration.datum frame).component with
 | none => exact .refl _
 | some old =>
   exact SourceNativeProjectionLaw.InstallationAt.componentCoface
     ({(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base with projectionLaw:=old})
     (stockLaw frame configuration)
def installed := (stockEmbedding (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base
  (component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (programme configuration)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (programme configuration))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame (programme configuration)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (programme configuration))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame (programme configuration)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (programme configuration))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame (programme configuration)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (programme configuration)))
def sourceOutcome :=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root frame (programme configuration)).source.base.projectionLaw.outcomeAt
 ((installed frame configuration).embed PUnit.unit)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)
theorem source_inventory : HEq (sourceOutcome frame configuration)
 (Sum.inl (β:=PEmpty.{u+1}) (⟨PUnit.unit,completeMaterial (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)⟩ :
  Sigma fun active : (stockLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration).ActiveAt PUnit.unit
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) =>
   (stockLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration).PayloadAt PUnit.unit
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) active)) :=
 (installed frame configuration).outcome_heq
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) PUnit.unit
end SourceGeneratedInquiryReceiptAction.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
