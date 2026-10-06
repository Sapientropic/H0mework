import H0mework.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Embedding
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.Fresh
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Source
import H0mework.Realization.Operations.Execution.Relations.History.Events

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch (outcome nextOutcome)
namespace Fresh
export SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh (Complete Outcome.complete)
end Fresh
end B
namespace Q
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery (Value Variable raw expression environment)
end Q
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RootLawDependentJointStateController.RecognitionAt H root)
abbrev Carrier := B.Fresh.Complete root recognition
abbrev ActorValue := (Carrier root recognition →₀ ℤ) × (Carrier root recognition →₀ ℤ)
abbrev Output := Q.Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result × ActorValue root recognition
abbrev Value := Extension.Value (Q.Value root visit recognition) (Output root visit recognition)
abbrev Variable := Extension.Var (Q.Variable root visit recognition)
def completeMap : (SourceOperationNative.Tree.Fold.Dependent.Branch.Outcome root visit recognition →₀ ℤ) →+
    (Carrier root recognition →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (B.Fresh.Outcome.complete root recognition visit)
def completePairMap := (completeMap root visit recognition).prodMap (completeMap root visit recognition)
def actorProjection : Q.Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result →+
    ActorValue root recognition where
  toFun value := completePairMap root visit recognition (value 0)
  map_zero' := (completePairMap root visit recognition).map_zero
  map_add' left right := (completePairMap root visit recognition).map_add (left 0) (right 0)
def projection : Q.Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result →+ Output root visit recognition :=
  (AddMonoidHom.id _).prod (actorProjection root visit recognition)
def expression : Expr (Value root visit recognition) (Variable root visit recognition) (.inr PUnit.unit) :=
  .linear (projection root visit recognition)
    (Extension.embed (Q.Value root visit recognition) (Q.Variable root visit recognition)
      (Output root visit recognition) (Q.expression root visit recognition))
abbrev environment := Extension.environment (Q.Value root visit recognition)
  (Q.Variable root visit recognition) (Output root visit recognition) (Q.environment root visit recognition)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=.inr PUnit.unit) :=
  ⟨environment root visit recognition,expression root visit recognition⟩
def reader {_current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt _current) := raw root visit recognition
abbrev originalPaid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  root.toAuthoritativeRoot (fun {_current} _ => Q.raw root visit recognition) (root.emitted visit.current)
abbrev paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  root.toAuthoritativeRoot (reader root visit recognition) (root.emitted visit.current)
def trace := execution (environment root visit recognition) (expression root visit recognition)
abbrev oldActor := B.Fresh.Outcome.complete root recognition visit (B.outcome root visit recognition)
abbrev nextActor := B.Fresh.Outcome.complete root recognition visit (B.nextOutcome root visit recognition)
abbrev actorVisit := SourceOperationNative.Tree.Fold.Dependent.Branch.Side.visit root (nextActor root visit recognition).1.1
def material := (originalPaid root visit recognition,paid root visit recognition,
  SourceOperationPaidRelations.exposure (originalPaid root visit recognition).2.1.2,
  SourceOperationPaidRelations.exposure (paid root visit recognition).2.1.2,
  nextActor root visit recognition)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
