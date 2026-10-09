import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Transport
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
abbrev runtime (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) := Shared.runtime initial (configuration seed)

variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev frameAt (count : Nat) := Shared.frames initial (configuration seed) count

theorem queryAt (count : Nat) : type_of% (Shared.actual_query initial (configuration seed) count) :=
  Shared.actual_query initial (configuration seed) count

theorem answerAt (count : Nat) : type_of% (Shared.actual_answer initial (configuration seed) count) :=
  Shared.actual_answer initial (configuration seed) count

theorem nextAt (count : Nat) : type_of% (Shared.actual_next initial (configuration seed) count) :=
  Shared.actual_next initial (configuration seed) count

theorem no_refill (count : Nat) : type_of% (Payment.Shared.no_refill (configuration seed) (frameAt seed initial count)) :=
  Payment.Shared.no_refill (configuration seed) (frameAt seed initial count)

theorem noetherian (count : Nat) : type_of% (Payment.Shared.wellFounded (configuration seed) (frameAt seed initial count)) :=
  Payment.Shared.wellFounded (configuration seed) (frameAt seed initial count)


theorem full_inventory (first distance : Nat) :
    ∀ atom ∈ (updatedSeed seed (epoch (frameAt seed initial first)) (Shared.actualOccurrence (frameAt seed initial first))).trace,
    atom ∈ (updatedSeed seed (epoch (frameAt seed initial (first+distance)))
      (Shared.actualOccurrence (frameAt seed initial (first+distance)))).trace := by
  induction distance with
  | zero => exact fun _ belongs => belongs
  | succ distance previous =>
      intro atom belongs
      have next := inventory_next seed (frameAt seed initial (first+distance)) atom (previous atom belongs)
      have index : first+(distance+1) = (first+distance)+1 := by omega
      rw [index]
      exact next


abbrev physicalSource := Context.Native.Orbit.Installation.Activation.Observation.rawSource initial (configuration seed)
abbrev physicalField (count : Nat) := Context.Faces.Cofinal.Carrier (runtime seed initial) (physicalSource seed initial) count

abbrev outputAt (count : Nat) := readout seed (epoch (frameAt seed initial count))
  (Shared.actualOccurrence (frameAt seed initial count))
  (disposition seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count)))
abbrev generated := (runtime seed initial,outputAt seed initial,
  (fun count => transition seed (frameAt seed initial count)),physicalSource seed initial,physicalField seed initial)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
