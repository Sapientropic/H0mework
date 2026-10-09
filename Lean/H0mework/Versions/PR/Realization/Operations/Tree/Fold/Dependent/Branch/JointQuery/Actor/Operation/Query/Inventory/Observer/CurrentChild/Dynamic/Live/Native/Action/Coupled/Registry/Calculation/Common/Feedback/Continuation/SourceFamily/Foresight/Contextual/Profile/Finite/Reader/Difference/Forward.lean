import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Source
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Boundary
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference
namespace R
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual
 (cfg material expression literalWord after actual_raw actual_state actual_environment actual_increment)
end R
namespace Ps
export Lower.SourceFamily.Foresight.Contextual.Psi
 (receipt endpointFrame installedFace source_clock complete_fee budget)
end Ps
namespace P
export Lower.SourceFamily.Foresight.Paid
 (sourceEnv result paidTrace raw expression complete_fee all_paid_relations generated_new_kernel)
end P
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (root base baseRoot actualOccurrence actualVisit query)
end Q
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw authoritativeRoot)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation
 (resultAt sourceMaterialAt source_value source_history)
end O
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev Word:=Formal ℤ (PairValue (Lower.Value W (n+1))) X s
abbrev sourceTrace:=(Ps.installedFace binding n data.2 data.1).rootRead.state.2
abbrev sourceEnvironment:=(Ps.receipt binding n data.2 data.1).registered.input.environment
abbrev sourceExpression:=(Ps.receipt binding n data.2 data.1).registered.input.expression
abbrev sourceValue:=(Ps.installedFace binding n data.2 data.1).rootRead.value

def psiBoundary:Formal ℤ (Lower.Value W (n+1)) X s:=
 relationMap (R:=ℤ) (sourceEnvironment binding n data) (sourceTrace binding n data).relationWords

def motherBoundary:Word (W:=W) (X:=X) (s:=s) n:=
 relationMap (R:=ℤ) (P.sourceEnv binding n data) (P.paidTrace binding n data s (R.literalWord binding n data)).relationWords

def difference:Word (W:=W) (X:=X) (s:=s) n:=
 liftMap (R:=ℤ) (psiBoundary binding n data)-motherBoundary binding n data

def environment:=P.sourceEnv binding n data

def expression:Expr (PairValue (Lower.Value W (n+1))) X s:=Coefficients.expression (difference binding n data)

def raw:O.Raw (Value:=PairValue (Lower.Value W (n+1))) (Var:=X) (sort:=s):=
 ⟨environment binding n data,expression binding n data⟩

def event:PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s):=
 .generator (expression binding n data)
def tree:=RootedAccountedUnfolding.zero (event binding n data)

theorem source_boundary:psiBoundary binding n data=
 Finsupp.single (sourceExpression binding n data) (1:ℤ)-
 Finsupp.single (Expr.const (sourceValue binding n data)) (1:ℤ):=
 SourceRegisteredClaimBoundary.boundary (Ps.endpointFrame binding n data.2 data.1)
  (Ps.source_clock binding n data.2 data.1)

theorem full_source_fee:(sourceTrace binding n data).length=Ps.budget binding n data.2 data.1:=Ps.complete_fee _ _ _ _
theorem full_mother_fee:(P.paidTrace binding n data s (R.literalWord binding n data)).length=
 remaining (P.expression (W:=W) (X:=X) n s (R.literalWord binding n data)):=P.complete_fee _ _ _ _ _

theorem generated_word:difference binding n data=
 liftMap (R:=ℤ) (psiBoundary binding n data)-motherBoundary binding n data:=rfl

theorem renderer:evaluation (R:=ℤ) (environment binding n data)
 (Finsupp.single (expression binding n data) (1:ℤ))=
 evaluation (R:=ℤ) (environment binding n data) (difference binding n data):=by
 simp only [evaluation,Finsupp.linearCombination_single,one_smul]
 exact Coefficients.expression_eval _ _

abbrev sourceRoot:=(Q.root data.1 (R.cfg binding n data)).toAuthoritativeRoot

def result:=O.resultAt (sourceRoot binding n data) (fun {_current} _=>raw binding n data) (Q.actualOccurrence data.1)
abbrev trace:=(result binding n data).2.1.2
def written:=SourceOperationPaidRelations.exposure (trace binding n data)

theorem own_value:(result binding n data).2.2.1=evaluation (R:=ℤ) (environment binding n data) (difference binding n data):=
 (O.source_value _ _ _).trans (Coefficients.expression_eval _ _)
theorem own_fee:(trace binding n data).length=Coefficients.cost (difference binding n data):=
 (O.source_history _ _ _).trans (Coefficients.expression_remaining _)
theorem all_own_relations:(SourceOperationPaidRelations.words (trace binding n data)).length=(trace binding n data).length:=
 SourceOperationPaidRelations.complete_steps _

def fullMaterial:=(R.material binding n data,(Ps.installedFace binding n data.2 data.1).rootRead,
 P.result binding n data s (R.literalWord binding n data),result binding n data,
 fun step:Fin (Coefficients.cost (difference binding n data)+1)=>
  let root:=O.authoritativeRoot (sourceRoot binding n data) (Q.actualVisit data.1).current
   (fun _=>raw binding n data)
  O.sourceMaterialAt root
   (root.emitted (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
    (sourceRoot binding n data) (Q.actualVisit data.1).current (fun _=>raw binding n data) step.1)))

theorem source_event:event binding n data∈(tree binding n data).trace:=List.mem_cons_self

def append (prior:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s))):=
 SourceHistoryCommon.seed prior (tree binding n data)
theorem prior_preserved (prior:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s)))
 (entry) (present:entry∈prior.trace):entry∈(append binding n data prior).trace:=
 (SourceHistoryCommon.parallel_left _ _ _).1 _ present
theorem scheduled (prior:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s))):
 event binding n data∈(append binding n data prior).trace:=
 (SourceHistoryCommon.parallel_right _ _ _).1 _ (source_event binding n data)

def pairUpdate (prior : RootedAccountedUnfolding
    (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s))) :=
  SourceHistoryCommon.seed (tree binding n data) prior

theorem pairUpdate_root (prior : RootedAccountedUnfolding
    (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s))) :
    (pairUpdate binding n data prior).root = event binding n data := rfl

theorem pairUpdate_preserves (prior : RootedAccountedUnfolding
    (PresentedRelationEventAt (Expr (PairValue (Lower.Value W (n+1))) X s)))
    (entry) (present : entry ∈ prior.trace) :
    entry ∈ (pairUpdate binding n data prior).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 _ present
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference

namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming
def eventExpression {S : Type u} {Y Z : S → Type u} [∀ t, AddCommGroup (Y t)] {s : S}
    : PresentedRelationEventAt (Expr (PairValue Y) Z s) → Expr (PairValue Y) Z s
  | .generator raw => raw
  | .relation word => Coefficients.expression word

def calculationReader {S : Type u} {Y Z : S → Type u} [∀ t, AddCommGroup (Y t)] {s : S}
    (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := Y) (Var := Z) (sort := s))
    (datum : SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum
      (PhysicalValue := Y) (PhysicalVar := Z) (sort := s) Z frame) :=
  frame.pairInventory.map (fun tree =>
    fun {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
      frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) =>
      (⟨(datum.reader supplied).environment,
        Expr.add (datum.reader supplied).expression (eventExpression tree.root)⟩ :
       RootGeneratedDebtActivationJointSource.OwnerFree.Raw
          (Value := PairValue Y) (Var := Z) (sort := s)))
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
