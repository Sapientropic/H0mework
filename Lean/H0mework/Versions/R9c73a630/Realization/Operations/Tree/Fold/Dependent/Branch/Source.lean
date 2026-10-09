import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.Action.Installation
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Side
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev step := recognition.generateStepAt visit
abbrev selected := settlePassiveEffect (step root visit recognition)
abbrev Payload := D.FeedAt (step root visit recognition) (selected root visit recognition)
abbrev Node := Payload root visit recognition × SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot
namespace Fresh
abbrev step (packet : Side.Packet root recognition) := recognition.generateStepAt (Side.visit root packet.1)
abbrev Phase (packet : Side.Packet root recognition) := PassiveEffectDispositionAt (step root recognition packet)
abbrev selected (packet : Side.Packet root recognition) := settlePassiveEffect (step root recognition packet)
abbrev Feed (packet : Side.Packet root recognition) := D.FeedAt (step root recognition packet) (selected root recognition packet)
def feed (packet : Side.Packet root recognition) : Feed root recognition packet := D.sourceFeed (step root recognition packet)
end Fresh

structure Outcome where
  historical : Payload root visit recognition
  sides : SourceTemporalMaterial.Action.Result root × Side.Packet root recognition
  nativeFeed : Fresh.Feed root recognition sides.2
abbrev Outcome.fst (output : Outcome root visit recognition) := output.historical
abbrev Outcome.snd (output : Outcome root visit recognition) := output.sides
def node : Node root visit recognition :=
  ⟨D.sourceFeed (step root visit recognition), SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit⟩
def tree := RootedAccountedUnfolding.zero (node root visit recognition)
def constructor (datum : Node root visit recognition) (_children : List (Outcome root visit recognition)) : Outcome root visit recognition :=
  let packet := Side.packet root recognition datum.2
  ⟨datum.1, ⟨SourceTemporalMaterial.Action.actual root datum.2,packet⟩, Fresh.feed root recognition packet⟩
abbrev Value := F.Value (Node root visit recognition) (Outcome root visit recognition)
abbrev Variable := F.Var (Node root visit recognition)
def nextNode (datum : Node root visit recognition) : Node root visit recognition :=
  ⟨datum.1, (SourceTemporalMaterial.Action.nextCode root datum.2).getD datum.2⟩
def environment : Env (Value root visit recognition) (Variable root visit recognition) := F.environment
def updatedEnvironment : Env (Value root visit recognition) (Variable root visit recognition)
  | .origin, datum => Finsupp.single (nextNode root visit recognition datum) 1
  | .result, empty => PEmpty.elim empty
  | .children, empty => PEmpty.elim empty
abbrev delta := updatedEnvironment root visit recognition - environment root visit recognition
abbrev programme := F.program (constructor root visit recognition) (tree root visit recognition)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (Value root visit recognition))
    (Var:=Variable root visit recognition) (sort:=.result) :=
  ⟨pairEnvironment (environment root visit recognition) (delta root visit recognition), liftExpr (programme root visit recognition)⟩
def reader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) := raw root visit recognition
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
