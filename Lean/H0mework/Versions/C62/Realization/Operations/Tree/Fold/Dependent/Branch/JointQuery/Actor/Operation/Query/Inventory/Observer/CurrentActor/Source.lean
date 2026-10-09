import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch (Node node nextNode constructor)
namespace Fresh
export SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh (Outcome.complete)
end Fresh
end B
abbrev coreSlot : Observer.Slot root recognition := .inl (.inl (.inl (.inl .origin)))
abbrev actorSlot : Observer.Slot root recognition := .inl (.inl (.inl (.inr PUnit.unit)))
def actorTerm : Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (actorSlot root recognition) :=
  Observer.embed root visit recognition (Inventory.embed root visit recognition
    (Actor.Extension.embed (Actor.Value root visit recognition) (Actor.Variable root visit recognition)
      (Query.Output root visit recognition) (Actor.expression root visit recognition)))
def inventoryBirthCount : Nat → Nat
  | 0 => 0
  | count+1 => match (Inventory.Live.frameAt root visit recognition U7 calculus count).action with
    | .inr _ => inventoryBirthCount count
    | .inl _ => inventoryBirthCount count+1
variable (anchor : Nat)
def birthCount : Nat → Nat
  | 0 => inventoryBirthCount root visit recognition U7 calculus anchor
  | count+1 => match (Observer.Live.frameAt root visit recognition U7 calculus anchor count).action with
    | .inr _ => birthCount count
    | .inl _ => birthCount count+1

def corePointAt (stage : Nat) (datum : B.Node root visit recognition) :=
  ActiveRaw.activeEnvironment root visit recognition U7 calculus anchor stage (coreSlot root recognition) (datum,.old) (0:Fin 2)
def coreNodeAt (stage : Nat) :=
  (B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage]
    (B.node root visit recognition)
def actorAt (stage : Nat) := B.Fresh.Outcome.complete root recognition visit
  (B.constructor root visit recognition (coreNodeAt root visit recognition U7 calculus anchor stage) [])
def nextActorAt (stage : Nat) := B.Fresh.Outcome.complete root recognition visit
  (B.constructor root visit recognition (B.nextNode root visit recognition
    (coreNodeAt root visit recognition U7 calculus anchor stage)) [])

namespace Lower
variable (frame : Observer.Action.Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Observer.Action.C.Occurrence frame (current:=current))
def rawAt : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Observer.Value root visit recognition) (Var:=Observer.Variable root visit recognition) (sort:=actorSlot root recognition) :=
  ⟨Observer.Action.environmentAt root visit recognition frame supplied,actorTerm root visit recognition⟩
def paidAt := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Observer.Live.E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} occurrence => rawAt root visit recognition frame occurrence) supplied
end Lower

def rawAt (stage : Nat) := Lower.rawAt root visit recognition
  (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)
  (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))
def paidAt (stage : Nat) := Lower.paidAt root visit recognition
  (Observer.Live.frameAt root visit recognition U7 calculus anchor stage)
  (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor stage))
def traceAt (stage : Nat) := execution (rawAt root visit recognition U7 calculus anchor stage).environment
  (rawAt root visit recognition U7 calculus anchor stage).expression

def OriginLaw (stage : Nat) : Prop := ∀ datum : B.Node root visit recognition,
  corePointAt root visit recognition U7 calculus anchor stage datum =
    (Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage] datum) 1,
      Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage+1] datum) 1 -
      Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage] datum) 1)
def UniformOriginLaw (stage : Nat) : Prop :=
  let frame := Observer.Live.frameAt root visit recognition U7 calculus anchor stage
  ∀ (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered)
    (supplied : Observer.Action.C.Occurrence frame (current:=current)) (datum : B.Node root visit recognition),
    Observer.Action.environmentAt root visit recognition frame supplied (coreSlot root recognition) (datum,.old) (0:Fin 2) =
      (Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage] datum) 1,
        Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage+1] datum) 1 -
        Finsupp.single ((B.nextNode root visit recognition)^[birthCount root visit recognition U7 calculus anchor stage] datum) 1)
def ActorLaw (stage : Nat) : Prop := (paidAt root visit recognition U7 calculus anchor stage).2.2.1.2 =
  (Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1,
    Finsupp.single (nextActorAt root visit recognition U7 calculus anchor stage) 1 -
      Finsupp.single (actorAt root visit recognition U7 calculus anchor stage) 1)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
