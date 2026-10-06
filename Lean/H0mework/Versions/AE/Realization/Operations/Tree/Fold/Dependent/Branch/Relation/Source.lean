import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.RichConsumer
import H0mework.Realization.Operations.CochainComplex
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Completion.HistorySettlement
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarCochain
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev Word := Formal ℤ (Value root visit recognition) (ChangedVar (Variable root visit recognition)) .result
abbrev relationWord : Word root visit recognition := updateWord (R:=ℤ) (programme root visit recognition)
abbrev mixed := mixedEnvironment (environment root visit recognition) (delta root visit recognition)
abbrev relationExpression := SourceOperationExecution.Coefficients.expression (relationWord root visit recognition)
abbrev relationRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=ChangedVar (Variable root visit recognition)) (sort:=SourceOperationNative.Tree.Fold.Slot.result) :=
  ⟨mixed root visit recognition,relationExpression root visit recognition⟩
def relationReader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  relationRaw root visit recognition
abbrev complex := SourceOperationCochain.cochain (s:=SourceOperationNative.Tree.Fold.Slot.result)
  (environment root visit recognition) (delta root visit recognition)
abbrev homology := SourceOperationCochain.generatedHomology (s:=SourceOperationNative.Tree.Fold.Slot.result)
  (environment root visit recognition) (delta root visit recognition)

abbrev Generator := Expr (Value root visit recognition) (ChangedVar (Variable root visit recognition)) .result

def incomingSeed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt
    (Generator root visit recognition)) := .zero (.relation (relationWord root visit recognition))

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
