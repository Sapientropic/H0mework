import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.Consumer
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic (binding)
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow (Variable right rightBinding)
end L
end D
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
 (programme material)
end R
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence query root visit runtime process frames next nextBorn actual_node actual_next actual_query)
end Shared
end A
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
abbrev PhysicalValue := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Value root visit rec
abbrev PhysicalVar := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Variable root visit rec
abbrev LowValue := PairValue (PhysicalValue root visit rec)
abbrev LowVar := D.L.Variable (X:=PhysicalVar root visit rec)
abbrev sort := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.resultSlot root rec
local instance : ∀ slot, AddCommGroup (PhysicalValue root visit rec slot) := inferInstance
def lowBinding (slot) (name : LowVar root visit rec slot) : Expr (LowValue root visit rec) (LowVar root visit rec) slot :=
 match name with
 | .inl old => .var (.inl old)
 | .inr actual => D.L.right (liftExpr (D.binding root visit rec slot actual))
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (LowValue root visit rec) (LowVar root visit rec) (sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=LowValue root visit rec) (Var:=LowVar root visit rec) (sort:=sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev originalRaw := ((R.programme seed).datum frame).reader actual
-- The existing R query is a pair of LowValue. Its binding is itself lifted.
def pairBinding (slot) (name : LowVar root visit rec slot) := liftExpr (lowBinding root visit rec slot name)
def actualEnvironment := frame.environment
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence frame.registered frame.packetAt actual)
def nextEnvironment := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
 (lowBinding root visit rec) (actualEnvironment root visit rec frame actual)
def actionPairEnvironment := pairEnvironment (actualEnvironment root visit rec frame actual)
 (nextEnvironment root visit rec frame actual - actualEnvironment root visit rec frame actual)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (LowValue root visit rec)) (Var:=LowVar root visit rec) (sort:=sort root rec) :=
 ⟨actionPairEnvironment root visit rec frame actual,
  (originalRaw root visit rec seed frame actual).expression.subst (pairBinding root visit rec)⟩
def readNext := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
 (pairBinding root visit rec) (actionPairEnvironment root visit rec frame actual)
def sourceTrace := execution (readNext root visit rec frame actual)
 (originalRaw root visit rec seed frame actual).expression
def replayTrace := (sourceTrace root visit rec seed frame actual).substitutedTrace
 (pairBinding root visit rec) (actionPairEnvironment root visit rec frame actual)
def paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (A.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => raw root visit rec seed frame occurrence) actual
def written := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure (paid root visit rec seed frame actual).2.1.2)
 (SourceOperationPaidRelations.exposure (replayTrace root visit rec seed frame actual))
def material := (R.material seed frame actual,pairBinding root visit rec,
 raw root visit rec seed frame actual,paid root visit rec seed frame actual,
 sourceTrace root visit rec seed frame actual,replayTrace root visit rec seed frame actual,
 readNext root visit rec frame actual,written root visit rec seed frame actual)
def physicalRaw := SourceOperationInquiry.Context.Installation.rawAt frame actual
def physicalNext := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
 (lowBinding root visit rec) (actualEnvironment root visit rec frame actual)
def physicalActionRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=LowValue root visit rec) (Var:=LowVar root visit rec) (sort:=sort root rec) :=
 ⟨(actualEnvironment root visit rec frame actual),
  (physicalRaw root visit rec frame actual).expression.subst (lowBinding root visit rec)⟩
def physicalActionTrace := execution (physicalNext root visit rec frame actual)
 (physicalRaw root visit rec frame actual).expression
def physicalReplay := (physicalActionTrace root visit rec frame actual).substitutedTrace
 (lowBinding root visit rec) (actualEnvironment root visit rec frame actual)
def physicalWritten := SourceHistoryCommon.seed
 (match frame.inventory with
 | none => seed
 | some prior => SourceHistoryCommon.seed seed prior)
 (SourceOperationPaidRelations.exposure (physicalReplay root visit rec frame actual))
def scalarWritten := match (R.programme seed).nextInventory frame with
 | none => physicalWritten root visit rec seed frame actual
 | some original => SourceHistoryCommon.seed original (physicalWritten root visit rec seed frame actual)
def pairWritten := match (R.programme seed).nextPairInventory frame with
 | none => written root visit rec seed frame actual
 | some original => SourceHistoryCommon.seed original (written root visit rec seed frame actual)
def actualRaw : SourceOperationInquiry.Context.Raw
 (PhysicalValue:=LowValue root visit rec) (PhysicalVar:=LowVar root visit rec) (sort:=sort root rec) :=
 ⟨actualEnvironment root visit rec frame actual,(physicalRaw root visit rec frame actual).expression⟩
def rightOldEnvironment := fun slot (name : PhysicalVar root visit rec slot) =>
 (actualEnvironment root visit rec frame actual slot (.inr name)).1
def rightEffectEnvironment := fun slot (name : PhysicalVar root visit rec slot) =>
 (actualEnvironment root visit rec frame actual slot (.inr name)).2

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
