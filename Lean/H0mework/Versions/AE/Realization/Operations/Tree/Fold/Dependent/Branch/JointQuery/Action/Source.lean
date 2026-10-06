import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Source
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

abbrev binding : ∀ target, JointQuery.Variable root visit recognition target →
    Expr (JointQuery.Value root visit recognition) (JointQuery.Variable root visit recognition) target :=
  fun target name => InventoryVector.expression (Fin 2)
    (liftExpr (Relation.Action.binding root visit recognition target name))
abbrev sourceEnvironment := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
  (binding root visit recognition) (JointQuery.environment root visit recognition)
abbrev increment := sourceEnvironment root visit recognition - JointQuery.environment root visit recognition
abbrev followingMixed := SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
  (Relation.Action.binding root visit recognition) (Relation.Action.environment root visit recognition)
abbrev expression := (JointQuery.expression root visit recognition).subst (binding root visit recognition)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=JointQuery.Value root visit recognition) (Var:=JointQuery.Variable root visit recognition) (sort:=.result) :=
  ⟨JointQuery.environment root visit recognition, expression root visit recognition⟩
def updatedRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=JointQuery.Value root visit recognition) (Var:=JointQuery.Variable root visit recognition) (sort:=.result) :=
  ⟨sourceEnvironment root visit recognition, JointQuery.expression root visit recognition⟩
def sourceTrace := execution (sourceEnvironment root visit recognition) (JointQuery.expression root visit recognition)
def fullTrace := (sourceTrace root visit recognition).substitutedTrace
  (binding root visit recognition) (JointQuery.environment root visit recognition)
def material := (Relation.Action.material root visit recognition, binding root visit recognition,
  sourceEnvironment root visit recognition, raw root visit recognition, fullTrace root visit recognition)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
