import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.Source
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end Shared
end E
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end C
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)

def binding : ∀ slot, Observer.Variable root visit recognition slot →
    Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) slot
  | .inl slot, name => Observer.embed root visit recognition (Inventory.Action.binding root visit recognition slot name)
  | .inr _, absent => PEmpty.elim absent
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
abbrev Frame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Observer.Value root visit recognition) (Var:=Observer.Variable root visit recognition)
  (sort:=Observer.resultSlot root recognition)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : C.Occurrence frame (current:=current))
abbrev environmentAt := frame.environment
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
    frame.registered frame.packetAt occurrence)
def oldEnvironmentAt : Env (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) :=
  fun slot name => environmentAt root visit recognition frame occurrence (.inl slot) name
abbrev generatedEnvironmentAt := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
  (binding root visit recognition) (environmentAt root visit recognition frame occurrence)
abbrev incrementAt := generatedEnvironmentAt root visit recognition frame occurrence -
  environmentAt root visit recognition frame occurrence
-- The source catalogue and physical M/U stay fixed; its syntax executes in the actual supplied environment.
def observerSyntax := (Observer.raw root visit recognition U7 calculus anchor).expression
def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Observer.Value root visit recognition) (Var:=Observer.Variable root visit recognition)
    (sort:=Observer.resultSlot root recognition) :=
  ⟨environmentAt root visit recognition frame occurrence,
    (observerSyntax root visit recognition U7 calculus anchor).subst (binding root visit recognition)⟩
def sourceTraceAt := execution (generatedEnvironmentAt root visit recognition frame occurrence)
  (observerSyntax root visit recognition U7 calculus anchor)
def fullTraceAt := (sourceTraceAt root visit recognition U7 calculus anchor frame occurrence).substitutedTrace
  (binding root visit recognition) (environmentAt root visit recognition frame occurrence)
abbrev paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} supplied => rawAt root visit recognition U7 calculus anchor frame supplied) occurrence
def writtenAt := SourceHistoryCommon.seed
  (SourceOperationPaidRelations.exposure (paidAt root visit recognition U7 calculus anchor frame occurrence).2.1.2)
  (SourceOperationPaidRelations.exposure (fullTraceAt root visit recognition U7 calculus anchor frame occurrence))
def materialAt := (C.materialAt frame occurrence, binding root visit recognition,
  rawAt root visit recognition U7 calculus anchor frame occurrence,
  paidAt root visit recognition U7 calculus anchor frame occurrence,
  fullTraceAt root visit recognition U7 calculus anchor frame occurrence,
  generatedEnvironmentAt root visit recognition frame occurrence)
abbrev generatedEnvironment := generatedEnvironmentAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev increment := incrementAt root visit recognition frame (E.Shared.actualOccurrence frame)
abbrev written := writtenAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev material := materialAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)
abbrev initial := Observer.Installation.initial root visit recognition U7 calculus anchor
abbrev sourceSeed := Observer.Installation.seed root visit recognition U7 calculus anchor
abbrev raw := rawAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
  (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))
abbrev sourceTrace := sourceTraceAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
  (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))
abbrev fullTrace := fullTraceAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
  (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))
abbrev paid := paidAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
  (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))
abbrev sourceMaterial := material root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
abbrev sourceAction := (sourceSeed root visit recognition U7 calculus anchor,
  sourceMaterial root visit recognition U7 calculus anchor)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
