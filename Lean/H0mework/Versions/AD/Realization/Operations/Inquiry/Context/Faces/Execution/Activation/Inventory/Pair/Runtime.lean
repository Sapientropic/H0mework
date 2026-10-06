import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Transport
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev runtime := Shared.runtime initial (programme seed)
abbrev frameAt (count : Nat) := Shared.frames initial (programme seed) count
abbrev outputAt (count : Nat) := readout seed (epoch (frameAt seed initial count))
  (Shared.actualOccurrence (frameAt seed initial count))
  (disposition seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count)))
abbrev physicalSource := Context.Native.Orbit.Installation.Activation.Observation.rawSource initial (programme seed)
abbrev physicalField (count : Nat) := Context.Faces.Cofinal.Carrier (runtime seed initial) (physicalSource seed initial) count

theorem actual_query (count : Nat) : type_of% (Shared.actual_query initial (programme seed) count) :=
  Shared.actual_query initial (programme seed) count

theorem actual_answer (count : Nat) : type_of% (Shared.actual_answer initial (programme seed) count) :=
  Shared.actual_answer initial (programme seed) count

theorem actual_next (count : Nat) : type_of% (Shared.actual_next initial (programme seed) count) :=
  Shared.actual_next initial (programme seed) count

theorem physical_source (count : Nat) : type_of% (Context.Native.Orbit.Installation.Activation.Observation.raw_actual
    initial (programme seed) count) := Context.Native.Orbit.Installation.Activation.Observation.raw_actual initial (programme seed) count

theorem full_history_preserved (first distance : Nat) :
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


theorem actual_no_refill (count : Nat) : type_of%
    (Payment.Shared.no_refill (programme seed) (frameAt seed initial count)) :=
  Payment.Shared.no_refill (programme seed) (frameAt seed initial count)

theorem actual_noetherian (count : Nat) : type_of%
    (Payment.Shared.wellFounded (programme seed) (frameAt seed initial count)) :=
  Payment.Shared.wellFounded (programme seed) (frameAt seed initial count)

theorem actual_debt_current (count : Nat) : type_of%
    (Payment.Shared.macro_current (programme seed) initial count) :=
  Payment.Shared.macro_current (programme seed) initial count

abbrev generated := (runtime seed initial,outputAt seed initial,
  (fun count => transition seed (frameAt seed initial count)),physicalField seed initial)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
