import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport.SourceGeneratorAdmission
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace AR
export SourceInventoryExecutionFeed.AdmissionReceipt (GeneratorOccurrence)
end AR
namespace SA
export ActualCofinalSourceAction (sourceLiftEvent selected nativePacket)
end SA
namespace L
export ActualCofinalSourceAction.L (Value groups)
end L
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target

def sourceExpression
 (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W:=W) (X:=X) (s:=s))
 (expression : Expr (L.Value W packet.1) X s) :
 Expr (L.Value W (packet.1+1)) packet.2.2.1.LowVar s := by
 letI : ∀ target,AddCommGroup (L.Value W packet.1 target) := L.groups W packet.1
 exact packet.2.2.2.down.symm ▸ liftExpr (Value:=L.Value W packet.1) (Var:=X) expression

private theorem transported_generator {V Y Z : Sorts → Type u} [∀ target,AddCommGroup (V target)]
 (same : Y=Z) (expression : Expr V Z s) :
 (same.symm ▸ ActualCofinalSourceAction.T.liftEvent
   (PresentedRelationEventAt.generator expression))=
 PresentedRelationEventAt.generator (same.symm ▸ liftExpr expression) := by
 cases same
 rfl

/-- Literal source transport preserves this generator's generated position, including repeated syntax. -/
def generator
 (factory : ActualCofinalSourceAction.SF.Factory W X s)
 (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W:=W) (X:=X) (s:=s))
 (prior : SourceInventoryExecutionFeed.Inventory (V:=L.Value W packet.1) (X:=X) (s:=s))
 (present : packet.2.1.1.inventory=some prior)
 (occurrence : AR.GeneratorOccurrence prior) :
 AR.GeneratorOccurrence (AS.stockScalar (SA.selected factory packet) (SA.nativePacket factory packet).2.2.1) := by
 let block:=SourceInventoryBlock.source factory packet prior present
 refine ⟨block.before++occurrence.before.map (SA.sourceLiftEvent packet),
  sourceExpression packet occurrence.expression,
  occurrence.after.map (SA.sourceLiftEvent packet)++block.after,?_⟩
 have mapped : prior.trace.map (SA.sourceLiftEvent packet)=
   occurrence.before.map (SA.sourceLiftEvent packet)++
    PresentedRelationEventAt.generator (sourceExpression packet occurrence.expression)::
     occurrence.after.map (SA.sourceLiftEvent packet) := by
  rw [occurrence.trace_eq,List.map_append,List.map_cons]
  rw [show SA.sourceLiftEvent packet (.generator occurrence.expression)=
   .generator (sourceExpression packet occurrence.expression) from
    by simpa only [SA.sourceLiftEvent,sourceExpression] using
     transported_generator packet.2.2.2.down occurrence.expression]
 exact block.trace_eq.trans
  ((congrArg (fun middle=>block.before++middle++block.after) mapped).trans
   (by simp only [List.cons_append,List.append_assoc]))

theorem generator_expression
 (factory : ActualCofinalSourceAction.SF.Factory W X s)
 (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W:=W) (X:=X) (s:=s))
 (prior : SourceInventoryExecutionFeed.Inventory (V:=L.Value W packet.1) (X:=X) (s:=s))
 (present : packet.2.1.1.inventory=some prior) (occurrence : AR.GeneratorOccurrence prior) :
 (generator factory packet prior present occurrence).expression=sourceExpression packet occurrence.expression := rfl

end ActualNativeRelationTransport.SourceGeneratorAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
