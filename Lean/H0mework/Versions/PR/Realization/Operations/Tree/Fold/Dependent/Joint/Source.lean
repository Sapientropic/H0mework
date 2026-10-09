import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Realization.Operations.Tree.Fold.Inverse
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.Action.Consumer
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.RootSource
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Source
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev step := recognition.generateStepAt visit
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
abbrev OriginalRoot := AlignedJointPayloadAt (step root visit recognition) successor transition.history
abbrev OriginalResult := TreeOutcomeAt (step root visit recognition) successor transition.history
abbrev Node := OriginalRoot root visit recognition successor transition × SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot
abbrev Outcome := OriginalResult root visit recognition successor transition ×
  RootedAccountedUnfolding (T.Result root) × SourceHistoryCommon.Root.Raw root visit recognition successor ×
  SourceHistoryCommon.Root.Evaluator.Result root visit recognition successor ×
  SourceHistoryCommon.Root.Action.Plan root visit recognition successor
def tree : RootedAccountedUnfolding (Node root visit recognition successor transition) :=
  (D.nativeTree (step root visit recognition) successor transition alignment).map
    (fun node => (node, SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit))
def branchesOfList {X : Type u} : List (RootedAccountedUnfolding X) → AccountedBranches X
  | [] => .nil
  | head :: rest => .cons head (branchesOfList rest)
def constructor (node : Node root visit recognition successor transition)
    (children : List (Outcome root visit recognition successor transition)) : Outcome root visit recognition successor transition :=
  (effectFoldAt (step root visit recognition) successor transition.history node.1 (children.map Prod.fst),
    .occur (T.actual root node.2) (branchesOfList (children.map (fun child => child.2.1))),
    SourceHistoryCommon.Root.combine root visit recognition successor
      (SourceHistoryCommon.Root.sourceRaw root visit recognition)
      (SourceHistoryCommon.Root.targetRaw root visit recognition successor),
    SourceHistoryCommon.Root.Evaluator.combine root visit recognition successor
      (SourceHistoryCommon.Root.Evaluator.source root visit recognition)
      (SourceHistoryCommon.Root.Evaluator.target root visit recognition successor),
    SourceHistoryCommon.Root.Action.combine root visit recognition successor
      (SourceHistoryCommon.Root.Action.sourceExposure root visit recognition)
      (SourceHistoryCommon.Root.Action.targetExposure root visit recognition successor))
abbrev Value := F.Value (Node root visit recognition successor transition) (Outcome root visit recognition successor transition)
abbrev Variable := F.Var (Node root visit recognition successor transition)
def nextNode (node : Node root visit recognition successor transition) : Node root visit recognition successor transition :=
  (node.1, (T.nextCode root node.2).getD node.2)
def updatedEnvironment : Env (Value root visit recognition successor transition) (Variable root visit recognition successor transition)
  | .origin, node => Finsupp.single (nextNode root visit recognition successor transition node) 1
  | .result, name => PEmpty.elim name
  | .children, name => PEmpty.elim name
abbrev delta := updatedEnvironment root visit recognition successor transition - F.environment
abbrev programme := F.program (constructor root visit recognition successor transition)
  (tree root visit recognition successor transition alignment)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root visit recognition successor transition))
    (Var:=Variable root visit recognition successor transition) (sort:=.result) :=
  ⟨SourceOperationScalarInventoryLift.pairEnvironment F.environment (delta root visit recognition successor transition),
    SourceOperationScalarInventoryLift.liftExpr (programme root visit recognition successor transition alignment)⟩
abbrev reader := fun (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) =>
  raw root visit recognition successor transition alignment
abbrev sourceOutcome := (tree root visit recognition successor transition alignment).fold (constructor root visit recognition successor transition)
abbrev targetOutcome := ((tree root visit recognition successor transition alignment).map (nextNode root visit recognition successor transition)).fold
  (constructor root visit recognition successor transition)
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
