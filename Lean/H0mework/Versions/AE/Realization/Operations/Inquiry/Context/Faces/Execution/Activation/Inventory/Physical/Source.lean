import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Runtime
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Relations
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Fibre
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Physical
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
  (rawSource raw_actual stage_actual character_source_read character_next_read complete_source_word actual_source_receipt)
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev source := O.rawSource initial (programme seed)
abbrev fullHistory (offset : Nat) := Context.History.completion (runtime seed initial) (source seed initial) offset
abbrev fullField (offset : Nat) := Context.Faces.Cofinal.Carrier (runtime seed initial) (source seed initial) offset
abbrev fieldSource (offset : Nat) := Context.Faces.Cofinal.sourceMap (runtime seed initial) (source seed initial) offset
abbrev fieldNext (offset : Nat) := Context.Faces.Cofinal.next (runtime seed initial) (source seed initial) offset
abbrev actualWord (count : Nat) := (materialFace seed (frameAt seed initial count)).rootRead.2.2.2.2.1
abbrev wordField (count : Nat) := fieldSource seed initial count (actualWord seed initial count)

abbrev WordFibre (count : Nat) := SourceOperationLogic.Fibre (fieldSource seed initial count)
  (SourceOperationLogic.q (fieldSource seed initial count) (actualWord seed initial count))
def wordWitness (count : Nat) : WordFibre seed initial count := SourceOperationLogic.sourceWitness _ _

abbrev fibreAction (count : Nat) := Context.Faces.actualMorphism (runtime seed initial) (source seed initial)
  ((runtime seed initial).stateAt count)
abbrev recover (count : Nat) := Context.Faces.recover (runtime seed initial) (source seed initial)
  ((runtime seed initial).stateAt count)


abbrev generated := (fullHistory seed initial,wordField seed initial,fieldNext seed initial,wordWitness seed initial,
  fibreAction seed initial,recover seed initial)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Physical
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
