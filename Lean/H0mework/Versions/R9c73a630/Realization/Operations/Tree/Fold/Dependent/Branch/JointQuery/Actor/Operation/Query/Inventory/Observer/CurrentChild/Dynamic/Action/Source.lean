import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Source
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace E.Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end E.Shared
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence)
end C
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev Frame := Dynamic.Frame root visit recognition
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : C.Occurrence frame (current:=current))
abbrev environmentAt := Dynamic.environmentAt root visit recognition frame supplied
abbrev generatedEnvironmentAt := Dynamic.generatedEnvironmentAt root visit recognition frame supplied
abbrev incrementAt := generatedEnvironmentAt root visit recognition frame supplied - environmentAt root visit recognition frame supplied
abbrev nextExpressionAt := Dynamic.expressionFor root visit recognition U7 calculus anchor frame
 (Dynamic.nextRead root visit recognition frame) supplied

def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=CurrentChild.Value root visit recognition) (Var:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition) :=
 ⟨environmentAt root visit recognition frame supplied,
  (nextExpressionAt root visit recognition U7 calculus anchor frame supplied).subst (Dynamic.binding root visit recognition)⟩
def sourceTraceAt := execution (generatedEnvironmentAt root visit recognition frame supplied)
 (nextExpressionAt root visit recognition U7 calculus anchor frame supplied)
def fullTraceAt := (sourceTraceAt root visit recognition U7 calculus anchor frame supplied).substitutedTrace
 (Dynamic.binding root visit recognition) (environmentAt root visit recognition frame supplied)
def paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (E.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => rawAt root visit recognition U7 calculus anchor frame occurrence) supplied
def writtenAt := SourceHistoryCommon.seed
 (SourceOperationPaidRelations.exposure (paidAt root visit recognition U7 calculus anchor frame supplied).2.1.2)
 (SourceOperationPaidRelations.exposure (fullTraceAt root visit recognition U7 calculus anchor frame supplied))
def materialAt := ((Dynamic.materialAt root visit recognition U7 calculus anchor frame supplied,
 Dynamic.materialFor root visit recognition U7 calculus anchor frame (Dynamic.nextRead root visit recognition frame) supplied),
 Dynamic.binding root visit recognition,rawAt root visit recognition U7 calculus anchor frame supplied,
 paidAt root visit recognition U7 calculus anchor frame supplied,fullTraceAt root visit recognition U7 calculus anchor frame supplied,
 generatedEnvironmentAt root visit recognition frame supplied)
abbrev raw := rawAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev paid := paidAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev fullTrace := fullTraceAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev written := writtenAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev material := materialAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
variable (sourceStage : Nat)
abbrev sourceRaw := raw root visit recognition U7 calculus anchor (Dynamic.initial root visit recognition U7 calculus anchor sourceStage)
abbrev sourceMaterial := material root visit recognition U7 calculus anchor (Dynamic.initial root visit recognition U7 calculus anchor sourceStage)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
