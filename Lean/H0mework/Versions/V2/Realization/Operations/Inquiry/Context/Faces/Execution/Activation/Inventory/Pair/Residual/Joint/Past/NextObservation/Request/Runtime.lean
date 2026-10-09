import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J

abbrev inventoryRuntime (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) :=
  Shared.runtime initial (installedConfiguration seed)
abbrev frameAt (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :=
  Shared.frames initial (installedConfiguration seed) count

theorem queryAt (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :
    type_of% (Shared.actual_query initial (installedConfiguration seed) count) :=
  Shared.actual_query initial (installedConfiguration seed) count
theorem answerAt (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :
    type_of% (Shared.actual_answer initial (installedConfiguration seed) count) :=
  Shared.actual_answer initial (installedConfiguration seed) count
theorem nextAt (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :
    type_of% (Shared.actual_next initial (installedConfiguration seed) count) :=
  Shared.actual_next initial (installedConfiguration seed) count
theorem no_refill (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :
    type_of% (Payment.Shared.no_refill (installedConfiguration seed) (frameAt seed initial count)) :=
  Payment.Shared.no_refill (installedConfiguration seed) (frameAt seed initial count)
theorem noetherian (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) (count : Nat) :
    type_of% (Payment.Shared.wellFounded (installedConfiguration seed) (frameAt seed initial count)) :=
  Payment.Shared.wellFounded (installedConfiguration seed) (frameAt seed initial count)

theorem full_scalar_inventory (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
    (first distance : Nat) :
    ∀ event ∈ (updatedSeed seed (epoch (frameAt seed initial first))
      (Shared.actualOccurrence (frameAt seed initial first))).trace,
    event ∈ (updatedSeed seed (epoch (frameAt seed initial (first+distance)))
      (Shared.actualOccurrence (frameAt seed initial (first+distance)))).trace := by
  induction distance with
  | zero => exact fun _ belongs => belongs
  | succ distance previous =>
      intro event belongs
      exact scalar_inventory_next seed (frameAt seed initial (first+distance)) event (previous event belongs)

variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev requestFrame (count : Nat) := Shared.frames initial (installedConfiguration seed) count
abbrev physicalSource := Context.Native.Orbit.Installation.Activation.Observation.rawSource initial (installedConfiguration seed)
abbrev physicalField (count : Nat) := Context.Faces.Cofinal.Carrier (inventoryRuntime seed initial) (physicalSource seed initial) count
abbrev generated := (inventoryRuntime seed initial,
  fun count => Past.material seed (requestFrame seed initial count) (requestFrame seed initial count).depth,
  fun count => runtime seed (requestFrame seed initial count),
  fun count => completed seed (requestFrame seed initial count),
  fun count => installedWritten seed (requestFrame seed initial count),
  fun count => completionTransition seed (requestFrame seed initial count),
  fun count => output seed (requestFrame seed initial count),
  fun count => NextObservation.generated seed (requestFrame seed initial count),
  physicalSource seed initial,physicalField seed initial)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
