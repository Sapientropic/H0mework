import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Language
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor stage : Nat)
abbrev sourceFrame := Observer.Live.frameAt root visit recognition U7 calculus anchor stage
abbrev sourceOccurrence := Observer.Live.E.Shared.actualOccurrence (sourceFrame root visit recognition U7 calculus anchor stage)
abbrev sourceActor := CurrentActor.nextActorAt root visit recognition U7 calculus anchor stage
abbrev code := (sourceActor root visit recognition U7 calculus anchor stage).1.1
abbrev operation := Operation.sourceOperationAtCode root (code root visit recognition U7 calculus anchor stage) recognition
abbrev selectedIndices := indices root recognition (sourceActor root visit recognition U7 calculus anchor stage)
abbrev selectedSamples := samples root recognition (sourceActor root visit recognition U7 calculus anchor stage)
def oldOutputEmbed (term : Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition)
 (Observer.resultSlot root recognition)) : Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
 .linear (s:=.inl (Observer.resultSlot root recognition)) (oldInjection root visit recognition) (embed root visit recognition term)
def oldTerm := oldOutputEmbed root visit recognition (Observer.Action.observerSyntax root visit recognition U7 calculus anchor)
def actorTerm : Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
 .linear (s:=.inl (CurrentActor.actorSlot root recognition)) (actorInjection root visit recognition)
 (embed root visit recognition (CurrentActor.actorTerm root visit recognition))
def childTerm := oldOutputEmbed root visit recognition (Observer.oldOutputEmbed root visit recognition
 (Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)))
def observerTerms := ((selectedIndices root visit recognition U7 calculus anchor stage).map
 (fun index => List.ofFn (fun kind : Fin 4 => observationOutput root visit recognition index kind))).flatten
def gramTerms := (selectedSamples root visit recognition U7 calculus anchor stage).flatMap
 (fun first => (selectedSamples root visit recognition U7 calculus anchor stage).map
  (fun second => gramOutput root visit recognition first second))
def programme : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition)) →
 Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition)
 | [] => .const 0
 | first::rest => .add first (programme rest)
def expression := programme root visit recognition
 (oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
  childTerm root visit recognition U7 calculus anchor stage ::
  (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (sourceFrame root visit recognition U7 calculus anchor stage).registered}
variable (supplied : Observer.Action.C.Occurrence (sourceFrame root visit recognition U7 calculus anchor stage) (current:=current))
def environmentAt := Actor.Extension.environment (Observer.Value root visit recognition)
 (Observer.Variable root visit recognition) (Output root visit recognition)
 (Observer.Action.environmentAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied)
def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=resultSlot root recognition) :=
 ⟨environmentAt root visit recognition U7 calculus anchor stage supplied,expression root visit recognition U7 calculus anchor stage⟩
def paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (Observer.Live.E.Shared.base (sourceFrame root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot
 (fun {_current} occurrence => rawAt root visit recognition U7 calculus anchor stage occurrence) supplied
def traceAt := execution (rawAt root visit recognition U7 calculus anchor stage supplied).environment
 (rawAt root visit recognition U7 calculus anchor stage supplied).expression
def materialAt := (CurrentActor.Lower.paidAt root visit recognition
 (sourceFrame root visit recognition U7 calculus anchor stage) supplied,
 sourceActor root visit recognition U7 calculus anchor stage,operation root visit recognition U7 calculus anchor stage,
 selectedIndices root visit recognition U7 calculus anchor stage,
 fun position : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length =>
  let row := rowAt root recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩
  (Observer.sourceExposure root recognition row,Observer.targetExposure root recognition row),
 rawAt root visit recognition U7 calculus anchor stage supplied,paidAt root visit recognition U7 calculus anchor stage supplied,
 traceAt root visit recognition U7 calculus anchor stage supplied)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
