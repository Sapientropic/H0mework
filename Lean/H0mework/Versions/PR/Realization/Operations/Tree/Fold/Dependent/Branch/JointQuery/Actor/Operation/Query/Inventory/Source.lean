import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Language
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev oldCode := (Actor.oldActor root visit recognition).1.1
abbrev nextCode := (Actor.nextActor root visit recognition).1.1

def childExpressionAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  match stepSuccessor? (P.step root recognition code) with
  | none => .const 0
  | some successor => childOutput root visit recognition ⟨code,successor⟩
      (childRaw root recognition ⟨code,successor⟩).expression

def childCostAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) : Nat :=
  match stepSuccessor? (P.step root recognition code) with
  | none => 0
  | some successor => remaining (childRaw root recognition ⟨code,successor⟩).expression + 1

def expression : Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  .add (outputEmbed root visit recognition (Query.expression root visit recognition))
    (.add (childExpressionAtCode root visit recognition (oldCode root visit recognition))
      (childExpressionAtCode root visit recognition (nextCode root visit recognition)))
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=Variable root visit recognition) (sort:=resultSlot root recognition) :=
  ⟨environment root visit recognition,expression root visit recognition⟩
def reader {_current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt _current) := raw root visit recognition
def paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (reader root visit recognition) (root.emitted visit.current)
def trace := execution (environment root visit recognition) (expression root visit recognition)

-- Only the old/next selected subtrees execute. The dependent family is an ambient carrier.
def childTraceAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :=
  execution (environment root visit recognition) (childExpressionAtCode root visit recognition code)
def childValueAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :=
  (childExpressionAtCode root visit recognition code).eval (environment root visit recognition)

def oldEmbedding (term : Expr (Actor.Value root visit recognition) (Actor.Variable root visit recognition) (.inr PUnit.unit)) :
    Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
  outputEmbed root visit recognition (Query.embedOutput root visit recognition term)
def oldEventMap : PresentedRelationEventAt
    (Expr (Actor.Value root visit recognition) (Actor.Variable root visit recognition) (.inr PUnit.unit)) →
    PresentedRelationEventAt (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))
  | .generator term => .generator (oldEmbedding root visit recognition term)
  | .relation word => .relation (Finsupp.mapDomain (oldEmbedding root visit recognition) word)
abbrev oldStock := (Actor.Installation.stock root visit recognition).map (oldEventMap root visit recognition)
abbrev paidStock := SourceOperationPaidRelations.exposure (paid root visit recognition).2.1.2

def childEventMap (index : ChildIndex root recognition) : PresentedRelationEventAt
    (type_of% (childRaw root recognition index).expression) →
    PresentedRelationEventAt (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))
  | .generator term => .generator (childOutput root visit recognition index term)
  | .relation word => .relation (Finsupp.mapDomain (childOutput root visit recognition index) word)
def originalChildStock (index : ChildIndex root recognition) :=
  (SourceOperationPaidRelations.exposure
    (Operation.SomePacket.paid root recognition index.1 index.2 (childData root recognition index)
      (P.source_seed_eq root recognition index.1 index.2) (P.target_seed_eq root recognition index.1 index.2)).2.1.2).map
        (childEventMap root visit recognition index)
def liftedChildStock (index : ChildIndex root recognition) :=
  SourceOperationPaidRelations.exposure (execution (environment root visit recognition)
    (childOutput root visit recognition index (childRaw root recognition index).expression))
def childStockAtCode (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) : Option
    (RootedAccountedUnfolding (PresentedRelationEventAt
      (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition)))) :=
  match stepSuccessor? (P.step root recognition code) with
  | none => none
  | some successor => some (SourceHistoryCommon.seed (originalChildStock root visit recognition ⟨code,successor⟩)
      (liftedChildStock root visit recognition ⟨code,successor⟩))
def childStock := (childStockAtCode root visit recognition (oldCode root visit recognition),
  childStockAtCode root visit recognition (nextCode root visit recognition))
private def appendStock {T : Type u} (base : RootedAccountedUnfolding T) (child : Option (RootedAccountedUnfolding T)) :=
  match child with
  | none => base
  | some supplied => SourceHistoryCommon.seed base supplied

def stock := appendStock (appendStock (SourceHistoryCommon.seed (oldStock root visit recognition) (paidStock root visit recognition))
  (childStock root visit recognition).1) (childStock root visit recognition).2

def material := (Query.material root visit recognition,
  Operation.sourceOperationAtCode root (oldCode root visit recognition) recognition,
  Operation.sourceOperationAtCode root (nextCode root visit recognition) recognition,
  oldStock root visit recognition, childStock root visit recognition, stock root visit recognition,
  raw root visit recognition, paid root visit recognition, trace root visit recognition)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
