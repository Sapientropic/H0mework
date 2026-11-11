import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Stage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryStock

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
local instance receiptGroups (grade : Nat) : ∀ target,AddCommGroup (Lower.Value W grade target) := Lower.groups W grade
variable (factory : SF.Factory W X ()) (packet : AdmissionPacket (W:=W) (X:=X) (s:=()))
/-- Only the grade transport of this actual source-admission constructor is used. -/
def nativeAdmissionEvent
 (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W packet.1)) X ())) :
 PresentedRelationEventAt (Expr (Lower.Value W (nativeAfterAdmission factory packet).1) X ()) :=
 cast (congrArg (fun grade => PresentedRelationEventAt (Expr (Lower.Value W grade) X ()))
  (nativeAfterAdmission_grade factory packet).symm) event

/-- Every configured query event is present in this admission's literal native seed. -/
theorem native_seed_query_receipt
 (stock : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W packet.1)) X ())))
 (written : packet.2.2.1.nextPairInventory packet.2.1.1=some stock)
 (event) (belongs : event∈stock.trace) :
 nativeAdmissionEvent factory packet event∈(nativeAfterAdmission factory packet).2.1.2.trace := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  change event∈(nextSeed factory grade data ⟨X,datum,inventory,pairInventory⟩ rfl).trace
  exact next_seed_query_stock factory grade data _ rfl stock written event belongs

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
