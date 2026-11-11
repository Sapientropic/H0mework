import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CenteredGram.IntegralGraphJointAction

namespace Generic
variable {Sorts:Type} {U X:Sorts→Type} [∀t,AddCommGroup (U t)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=U) (Var:=X) (sort:=s))
variable (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=U) (PhysicalVar:=X) (sort:=s))
theorem paid_prefix_inventory (count:Nat) (within:count≤(S.Complete.receipt cfg frame 0).1):
 (S.frames frame cfg (0+count)).inventory=frame.inventory:=by
 induction count with
 | zero=>rfl
 | succ count previous=>
  have paid:=S.Prefix.receipt_paid_prefix cfg frame 0 ⟨count,by omega⟩
  have move:S.frames frame cfg (0+(count+1))=(S.frames frame cfg (0+count)).mathNext:=by
   change S.next (S.frames frame cfg (0+count)) cfg=_
   unfold S.next
   rw [paid.2.down]
  exact (congrArg (fun value:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
   (Value:=U) (Var:=X) (sort:=s)=>value.inventory) move).trans (previous (by omega))
end Generic

end CountedPaInitial.BornRWordPaWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
