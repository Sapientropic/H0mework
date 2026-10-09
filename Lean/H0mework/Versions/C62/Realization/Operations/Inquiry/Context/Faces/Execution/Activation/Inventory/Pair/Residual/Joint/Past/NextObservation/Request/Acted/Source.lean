import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
def material := (Joint.material seed frame occurrence,occurrenceRaw seed frame occurrence,
 occurrenceExecuted seed frame occurrence,Inverse.paidWritten seed frame occurrence,
 Inverse.result seed frame occurrence)
def component : SourceNativeProjectionLaw (Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} supplied _ => type_of% (material seed frame supplied)
 project := fun _ {_current} supplied _ => material seed frame supplied
-- Execute the source-generated request; its value retains its own unit.
def programme := {installedConfiguration seed with
 datum := fun sourceFrame => {
  component := some (component seed sourceFrame)
  reader := fun {_current} supplied => ((component seed sourceFrame).project PUnit.unit supplied PUnit.unit).2.1
  calculationReader := none }
 nextPairInventory := fun sourceFrame => some (SourceHistoryCommon.seed (Past.written seed sourceFrame)
  (((component seed (epoch sourceFrame)).project PUnit.unit (Shared.actualOccurrence sourceFrame) PUnit.unit).2.2.2.1)) }
def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Shared.base frame).root.source.base (component seed (epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame (programme seed)).source.base
  (Shared.queryLaw (epoch frame) (programme seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.queryRoot frame (programme seed)).source.base
  (Shared.resultLaw (epoch frame) (programme seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.resultRoot frame (programme seed)).source.base
  (Shared.consumerLaw (epoch frame) (programme seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.consumerRoot frame (programme seed)).source.base
  (Shared.compilationLaw (epoch frame) (programme seed)))
def face : SourceNativeRootSemanticFaceAt (Shared.root frame (programme seed)) (Shared.visit frame (programme seed)) where
 projection := (installation seed frame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev runtime := Shared.runtime initial (programme seed)
abbrev frameAt (count : Nat) := Shared.frames initial (programme seed) count
abbrev generated := (runtime seed initial,fun count => face seed (frameAt seed initial count))
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
