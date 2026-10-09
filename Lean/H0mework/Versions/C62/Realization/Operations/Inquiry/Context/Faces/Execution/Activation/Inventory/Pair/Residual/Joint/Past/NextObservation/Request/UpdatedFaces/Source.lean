import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Runtime
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Realization.Operations.ScalarComplex
import H0mework.Realization.Operations.ScalarExact
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
def rawRestriction : RawRestrictionAt (PhysicalValue:=PairValue PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort)
    (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered,
      ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt,
        (Shared.root frame (installedConfiguration seed)).toAuthoritativeRoot,
        Shared.visit frame (installedConfiguration seed)⟩⟩ : AnyAuthoritativeRootCurrent.{u}) where
  projection := (installed seed frame).embed (.inr (.inl PUnit.unit))
  active := PUnit.unit
  classifier_eq := rfl
  payload_eq := rfl
theorem raw_restriction : Context.Native.Orbit.Installation.Activation.Observation.readRaw _
    (rawRestriction seed frame) = occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame) := rfl

variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
def rawSource (state : (inventoryRuntime seed initial).State) :
    RawAt (PhysicalValue:=PairValue PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort)
      (inventoryRuntime seed initial) state := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact rawRestriction seed (frameAt seed initial count.down)
private def index (engine : Engine (Shared.process initial (installedConfiguration seed))) : Nat := by
  rcases engine with ⟨count⟩
  exact count.down

private theorem raw_state (state : (inventoryRuntime seed initial).State) :
    Context.raw (inventoryRuntime seed initial) (rawSource seed initial) state =
      occurrenceRaw seed (epoch (frameAt seed initial (index seed initial state.engine)))
      (Shared.actualOccurrence (frameAt seed initial (index seed initial state.engine))) := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact raw_restriction seed (frameAt seed initial count.down)

theorem raw_actual (count : Nat) :
    Context.raw (inventoryRuntime seed initial) (rawSource seed initial)
      ((inventoryRuntime seed initial).stateAt count) =
        occurrenceRaw seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count)) := by
  have indexEq : index seed initial ((inventoryRuntime seed initial).stateAt count).engine = count := by
    have same := Shared.actual_node initial (installedConfiguration seed) count
    generalize engineEq : ((inventoryRuntime seed initial).stateAt count).engine = engine at same ⊢
    rcases engine with ⟨hidden⟩
    have hiddenEq : hidden = ULift.up count := (Shared.process initial (installedConfiguration seed)).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase same)
    subst hidden
    rfl
  exact (raw_state seed initial _).trans
    (congrArg (fun count => occurrenceRaw seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count))) indexEq)

abbrev field (count : Nat) := Context.Faces.Cofinal.Carrier (inventoryRuntime seed initial)
  (rawSource seed initial) count
abbrev relationField (count : Nat) := Context.Faces.Cofinal.relationField (inventoryRuntime seed initial)
  (rawSource seed initial) count
abbrev successor (count : Nat) := Context.Faces.Cofinal.next (inventoryRuntime seed initial) (rawSource seed initial) count
theorem relation_read (count bound : Nat) (index : Fin (bound+1)) :
    type_of% (Context.Faces.Cofinal.relation_read (inventoryRuntime seed initial) (rawSource seed initial) count bound index) :=
  Context.Faces.Cofinal.relation_read (inventoryRuntime seed initial) (rawSource seed initial) count bound index
theorem full_fibre (count : Nat) (left right : Context.History.Words
    (PhysicalValue:=PairValue PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort)) :
    type_of% (Context.Faces.Cofinal.source_fibre (inventoryRuntime seed initial) (rawSource seed initial) count left right) :=
  Context.Faces.Cofinal.source_fibre (inventoryRuntime seed initial) (rawSource seed initial) count left right
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
