import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.Source
import H0mework.Realization.Logic.FibreLift
import H0mework.Realization.Logic.QuantifiedUpdate
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual SourceOperationLogic SourceOperationLogic.FibreLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev actualNext := Shared.next frame (continuedConfiguration seed)
abbrev before := Residual.raw seed (epoch frame) (Shared.actualOccurrence frame)
abbrev after := Residual.raw seed (epoch (actualNext seed frame)) (Shared.actualOccurrence (actualNext seed frame))
abbrev increment := (after seed frame).environment-(before seed frame).environment
abbrev full := updateInventory (R:=ℤ) (s:=sort) (before seed frame).environment (increment seed frame)
abbrev updated := evaluation (R:=ℤ) (s:=sort) (after seed frame).environment

def morphism : Morphism (full seed frame) (updated seed frame) where
  sourceMap := LinearMap.id
  targetMap := additionReadout (R:=ℤ)
  commutes := by
    have law := LinearMap.congr_fun (evaluation_update (R:=ℤ) (s:=sort)
      (before seed frame).environment (increment seed frame))
    apply LinearMap.ext
    intro word
    have environment : (before seed frame).environment + increment seed frame = (after seed frame).environment := add_sub_cancel _ _
    exact ((congrArg (fun binding => evaluation (R:=ℤ) (s:=sort) binding word) environment).symm.trans (law word)).symm

abbrev word := Finsupp.single (Shared.query frame (continuedConfiguration seed)).raw.expression (1 : ℤ)
abbrev originalValue := (full seed frame) (word seed frame)
abbrev actualTarget := (updated seed frame) (word seed frame)
abbrev inverse := mapFibre (morphism seed frame) (word seed frame)
abbrev residual := liftingResidual (morphism seed frame) (word seed frame)
abbrev generated := (morphism seed frame,word seed frame,originalValue seed frame,actualTarget seed frame,
  inverse seed frame,residual seed frame)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
