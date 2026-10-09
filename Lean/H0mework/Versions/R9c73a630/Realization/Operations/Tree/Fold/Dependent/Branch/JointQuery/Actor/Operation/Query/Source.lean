import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace A
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
  (Carrier ActorValue Output Value Variable expression environment paid oldActor nextActor)
end A
namespace O
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
  (ResultAt sourceOperationAtCode sourceOperation)
end O
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RootLawDependentJointStateController.RecognitionAt H root)
abbrev FunctionCarrier := Σ actor : A.Carrier root recognition,
  O.ResultAt root recognition actor.1.1
    (RootLawDependentJointTransition.stepSuccessor?
      (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.SomePacket.step
        root recognition actor.1.1))
def function (actor : A.Carrier root recognition) : FunctionCarrier root recognition :=
  ⟨actor,O.sourceOperationAtCode root actor.1.1 recognition⟩
abbrev FunctionPair := (FunctionCarrier root recognition →₀ ℤ) × (FunctionCarrier root recognition →₀ ℤ)
abbrev Output := A.Output root visit recognition × FunctionPair root recognition
abbrev Value := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.Value
  (A.Value root visit recognition) (Output root visit recognition)
abbrev Variable := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.Var
  (A.Variable root visit recognition)
def functionMap : (A.Carrier root recognition →₀ ℤ) →+ (FunctionCarrier root recognition →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (function root recognition)
def functionPairMap := (functionMap root recognition).prodMap (functionMap root recognition)
def projection : A.Output root visit recognition →+ Output root visit recognition :=
  (AddMonoidHom.id _).prod {
    toFun := fun source => functionPairMap root recognition source.2
    map_zero' := (functionPairMap root recognition).map_zero
    map_add' first second := (functionPairMap root recognition).map_add first.2 second.2 }
def expression : Expr (Value root visit recognition) (Variable root visit recognition) (.inr PUnit.unit) :=
  .linear (projection root visit recognition)
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed
      (A.Value root visit recognition) (A.Variable root visit recognition) (Output root visit recognition)
      (A.expression root visit recognition))
def environment := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.environment
  (A.Value root visit recognition) (A.Variable root visit recognition) (Output root visit recognition)
  (A.environment root visit recognition)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=.inr PUnit.unit) :=
  ⟨environment root visit recognition,expression root visit recognition⟩
def reader {_current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt _current) := raw root visit recognition
def paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (reader root visit recognition) (root.emitted visit.current)
def trace := execution (environment root visit recognition) (expression root visit recognition)
def material := (A.paid root visit recognition,paid root visit recognition,
  trace root visit recognition,O.sourceOperation root visit recognition)

def embedOutput (term : Expr (A.Value root visit recognition) (A.Variable root visit recognition) (.inr PUnit.unit)) :
    Expr (Value root visit recognition) (Variable root visit recognition) (.inr PUnit.unit) :=
  .linear ((AddMonoidHom.id _).prod 0)
    (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Extension.embed
      (A.Value root visit recognition) (A.Variable root visit recognition) (Output root visit recognition) term)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
