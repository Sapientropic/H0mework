import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport.SourceInventoryBlock

open SourceOperationEffects CofinalHistorySettlement

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
attribute [local instance] levelGroups
variable (factory : ActualCofinalSourceAction.SF.Factory W X s)
variable (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (prior : SourceInventoryExecutionFeed.Inventory (V := Lower.Value W packet.1) (X := X) (s := s))
variable (present : packet.2.1.1.inventory = some prior)

/-- The complete original inventory block survives the original Feed append, at its generated location. -/
def born : OccurrenceBlock (prior.trace.map (SA.sourceLiftEvent packet))
    (ActualCofinalSourceAction.bornStock factory packet).trace := by
  let block := source factory packet prior present
  let frame := ActualCofinalSourceAction.selected factory packet
  let configuration := (ActualCofinalSourceAction.nativePacket factory packet).2.2.1
  let target : SourceInventoryExecutionFeed.Inventory (V := Lower.Value W (packet.1+1))
      (X := packet.2.2.1.LowVar) (s := s) := AS.stockScalar frame configuration
  let environment : Env (Lower.Value W (packet.1+1)) packet.2.2.1.LowVar :=
    AS.stockDecodedEnvironment frame configuration
  let executions : List (SourceInventoryExecutionFeed.Event (V := Lower.Value W (packet.1+1))
      (X := packet.2.2.1.LowVar) (s := s)) := RootedAccountedUnfolding.traceBranches
    (SourceInventoryExecutionFeed.executionBranches environment (SourceInventoryExecutionFeed.requests target))
  refine ⟨block.before, block.after ++ executions, ?_⟩
  change (SourceInventoryExecutionFeed.written environment target).trace = _
  calc
    _ = target.trace ++ executions := SourceInventoryExecutionFeed.written_trace environment target
    _ = (block.before ++ prior.trace.map (SA.sourceLiftEvent packet) ++ block.after) ++ executions :=
      congrArg (· ++ executions) block.trace_eq
    _ = _ := by simp only [List.append_assoc]

end ActualNativeRelationTransport.SourceInventoryBlock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
