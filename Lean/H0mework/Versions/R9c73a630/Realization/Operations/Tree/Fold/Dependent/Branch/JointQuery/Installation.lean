import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Consumer
import H0mework.Realization.Operations.InventoryLift
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
open RootInquiryCompletion RootLawDependentJointStateController
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
def coreEmbedding (term : Expr (Inventory root visit recognition) (Branch.Variable root visit recognition) .result) :
 Expr (Value root visit recognition) (Variable root visit recognition) .result :=
 .linear (InventoryVector.mask (Fin 2) 0) (InventoryVector.expression (Fin 2) term.old)
def relationEmbedding (term : Expr (Branch.Value root visit recognition) (Variable root visit recognition) .result) :
 Expr (Value root visit recognition) (Variable root visit recognition) .result :=
 .linear (InventoryVector.mask (Fin 2) 1) (InventoryVector.expression (Fin 2) (liftExpr term))
private def eventMap {A B : Type u} (f : A → B) : PresentedRelationEventAt A → PresentedRelationEventAt B
 | .generator value => .generator (f value)
 | .relation values => .relation (Finsupp.mapDomain f values)
abbrev coreResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 root.toAuthoritativeRoot (fun {_current} _ => Branch.raw root visit recognition) (root.emitted visit.current)
abbrev relationResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 root.toAuthoritativeRoot (fun {_current} _ => Relation.relationRaw root visit recognition) (root.emitted visit.current)
abbrev batchResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 root.toAuthoritativeRoot (fun {_current} _ => raw root visit recognition) (root.emitted visit.current)
abbrev coreWritten := (SourceOperationPaidRelations.exposure (coreResult root visit recognition).2.1.2).map
 (eventMap (coreEmbedding root visit recognition))
abbrev relationWritten := (SourceOperationPaidRelations.exposure (relationResult root visit recognition).2.1.2).map
 (eventMap (relationEmbedding root visit recognition))
abbrev incoming := (Relation.incomingSeed root visit recognition).map (eventMap (relationEmbedding root visit recognition))
def jointSeed := SourceHistoryCommon.seed (SourceHistoryCommon.seed (incoming root visit recognition)
 (SourceHistoryCommon.seed (coreWritten root visit recognition) (relationWritten root visit recognition)))
 (SourceOperationPaidRelations.exposure (batchResult root visit recognition).2.1.2)
def material := (Branch.material root visit recognition,Relation.material root visit recognition,
 coreResult root visit recognition,relationResult root visit recognition,jointSeed root visit recognition,raw root visit recognition)
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material root visit recognition)
 project := fun _ {_current} _ _ => material root visit recognition
abbrev sourceRoot := (Branch.actualRoot root visit recognition).withProjectionCoface (component root visit recognition)
def installedReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
 ((component root visit recognition).project PUnit.unit occurrence PUnit.unit).2.2.2.2.2
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev fixedFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (sourceRoot root visit recognition) visit U7 calculus (installedReader root visit recognition)
abbrev initial := {fixedFrame root visit recognition U7 calculus with inventory:=some (jointSeed root visit recognition)}
abbrev seed := SourceHistoryCommon.seed (jointSeed root visit recognition)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
 (initial root visit recognition U7 calculus).registered.input.expression))
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
