import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
def pairEmbed {slot : Observer.Slot root recognition} :
 Expr (PairValue (Observer.Value root visit recognition)) (Observer.Variable root visit recognition) slot →
 Expr (PairValue (Value root visit recognition)) (Variable root visit recognition) (.inl slot)
 | .var name => .var name
 | .const value => .const value
 | .add first second => .add (pairEmbed first) (pairEmbed second)
 | @Expr.linear _ _ _ _ source target operation argument =>
   Expr.linear (Value:=PairValue (Value root visit recognition)) (Var:=Variable root visit recognition)
    (s:=.inl source) (t:=.inl target) operation (pairEmbed argument)
 | @Expr.bilinear _ _ _ _ firstSort secondSort target operation first second =>
   Expr.bilinear (Value:=PairValue (Value root visit recognition)) (Var:=Variable root visit recognition)
    (s:=.inl firstSort) (t:=.inl secondSort) (r:=.inl target) operation (pairEmbed first) (pairEmbed second)
def pairOutputEmbed (term : Expr (PairValue (Observer.Value root visit recognition)) (Observer.Variable root visit recognition)
 (Observer.resultSlot root recognition)) :
 Expr (PairValue (Value root visit recognition)) (Variable root visit recognition) (resultSlot root recognition) :=
 Expr.linear (Value:=PairValue (Value root visit recognition)) (Var:=Variable root visit recognition)
 (s:=.inl (Observer.resultSlot root recognition)) (t:=resultSlot root recognition)
 ((oldInjection root visit recognition).prodMap (oldInjection root visit recognition)) (pairEmbed root visit recognition term)
def eventMap : PresentedRelationEventAt (Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition)
 (Observer.resultSlot root recognition)) → PresentedRelationEventAt
 (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))
 | .generator term => .generator (oldOutputEmbed root visit recognition term)
 | .relation word => .relation (Finsupp.mapDomain (oldOutputEmbed root visit recognition) word)
def pairEventMap : PresentedRelationEventAt (Expr (PairValue (Observer.Value root visit recognition))
 (Observer.Variable root visit recognition) (Observer.resultSlot root recognition)) → PresentedRelationEventAt
 (Expr (PairValue (Value root visit recognition)) (Variable root visit recognition) (resultSlot root recognition))
 | .generator term => .generator (pairOutputEmbed root visit recognition term)
 | .relation word => .relation (Finsupp.mapDomain (pairOutputEmbed root visit recognition) word)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor stage : Nat)
abbrev originalFrame := sourceFrame root visit recognition U7 calculus anchor stage
abbrev sourceSeed := Observer.Live.sourceSeed root visit recognition U7 calculus anchor
abbrev mappedSeed := (sourceSeed root visit recognition U7 calculus anchor).map (eventMap root visit recognition)
abbrev mappedScalar := (Observer.Live.nextScalar root visit recognition U7 calculus anchor
 (originalFrame root visit recognition U7 calculus anchor stage) (sourceSeed root visit recognition U7 calculus anchor)).map
 (eventMap root visit recognition)
abbrev mappedPair := (Observer.Live.nextPair root visit recognition U7 calculus anchor
 (originalFrame root visit recognition U7 calculus anchor stage) (sourceSeed root visit recognition U7 calculus anchor)).map
 (pairEventMap root visit recognition)
abbrev paidStock := SourceOperationPaidRelations.exposure
 (paidAt root visit recognition U7 calculus anchor stage (sourceOccurrence root visit recognition U7 calculus anchor stage)).2.1.2
def stock := SourceHistoryCommon.seed (mappedSeed root visit recognition U7 calculus anchor)
 (SourceHistoryCommon.seed (mappedScalar root visit recognition U7 calculus anchor stage) (paidStock root visit recognition U7 calculus anchor stage))
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
