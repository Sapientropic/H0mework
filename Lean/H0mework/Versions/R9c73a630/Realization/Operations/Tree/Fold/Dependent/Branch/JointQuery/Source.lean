import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Action.Source
import H0mework.Realization.Operations.Execution.InventoryVector.Source
import H0mework.Realization.Operations.Execution.Run

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

abbrev Inventory := PairValue (Branch.Value root visit recognition)
abbrev Variable := ChangedVar (Branch.Variable root visit recognition)
abbrev Value := InventoryVector.VectorValue (Fin 2) (Value:=Inventory root visit recognition)

abbrev increment := Relation.Action.environment root visit recognition - Relation.mixed root visit recognition
abbrev sourceEnvironment := pairEnvironment (Relation.mixed root visit recognition) (increment root visit recognition)
abbrev coreTerm := (Branch.raw root visit recognition).expression.old
abbrev relationTerm := liftExpr (Relation.relationExpression root visit recognition)
def items : List (Fin 2 × Expr (Inventory root visit recognition) (Variable root visit recognition) .result) :=
  [(0, coreTerm root visit recognition), (1, relationTerm root visit recognition)]
abbrev expression := InventoryVector.query (Fin 2) (items root visit recognition)
abbrev environment := InventoryVector.environment (Fin 2) (sourceEnvironment root visit recognition)

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=.result) :=
  ⟨environment root visit recognition, expression root visit recognition⟩
def reader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  raw root visit recognition
def trace := execution (environment root visit recognition) (expression root visit recognition)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
