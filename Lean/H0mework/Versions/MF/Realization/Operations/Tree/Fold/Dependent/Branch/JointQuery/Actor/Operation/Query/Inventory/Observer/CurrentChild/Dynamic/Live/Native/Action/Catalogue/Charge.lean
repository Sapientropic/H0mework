import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Epoch.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Charge
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Act.LowValue root visit rec) (Act.LowVar root visit rec) (Act.sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem complete_query_charge :
 2≤remaining (queryRaw root visit rec U7 calculus anchor seed frame actual).expression := by
 change 2≤remaining (Act.raw root visit rec seed frame actual).expression+
  remaining (liftExpr (lowExpression root visit rec U7 calculus anchor frame actual))+1
 have catalogue : 2≤remaining (liftExpr (lowExpression root visit rec U7 calculus anchor frame actual)) := by
  unfold lowExpression D.Low.right expression terms
  change 2≤remaining (liftExpr ((liftExpr (Child.oldTerm root visit rec U7 calculus anchor)).subst
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.rightBinding))+
   (remaining (liftExpr ((liftExpr (Child.actorTerm root visit rec)).subst
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.rightBinding))+
    remaining (liftExpr ((liftExpr (Child.programme root visit rec
     (childTerms root visit rec frame actual ++ observationTerms root visit rec frame actual ++ gramTerms root visit rec frame actual))).subst
      SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.rightBinding))+1)+1
  omega
 omega
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Charge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
