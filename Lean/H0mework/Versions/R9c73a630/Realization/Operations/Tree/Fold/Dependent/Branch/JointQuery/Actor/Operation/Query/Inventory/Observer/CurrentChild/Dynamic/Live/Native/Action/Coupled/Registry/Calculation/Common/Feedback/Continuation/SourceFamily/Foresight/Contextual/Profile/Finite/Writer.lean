import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Native
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Indexed
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.Writer
namespace L
export Lower.SourceFamily.Foresight.Paid.Ledger (run run_contains writeEvent eventWord)
end L
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (origin:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
variable (point:GeneratedRelationResidualCoordinateAt (Indexed.face binding n seed frame origin))

def sourceTree (path:List PUnit.{u+1}) (k:Nat):=
 SourceHistoryCommon.seed
  (RootedAccountedUnfolding.zero (.generator
   (Coefficients.expression (actedWord binding n path point.relation))))
  (SourceOperationPaidRelations.exposure
   (profileResult binding n seed frame origin point path k).2.1.2)
def written (path:List PUnit.{u+1}) (k:Nat):=
 L.run (L.writeEvent binding n ⟨frame,seed⟩) (sourceTree binding n seed frame origin point path k)
def completed (path:List PUnit.{u+1}) (k:Nat):=
 SourceHistoryCommon.seed
  ((sourceTree binding n seed frame origin point path k).map T.liftEvent)
  (written binding n seed frame origin point path k)

private def selectedWrite {PathType:Type u} {Answer:Type u}
 {F G:PathType→Nat→Type u}
 (receipt:(Σpath:PathType,Σk:Nat,F path k)⊕(Σpath:PathType,Σk:Nat,G path k))
 (profile:(path:PathType)→(k:Nat)→F path k→Answer)
 (native:(path:PathType)→(k:Nat)→G path k→Answer):Answer:=
 Sum.casesOn receipt
 (fun chosen=>profile chosen.1 chosen.2.1 chosen.2.2)
 (fun chosen=>native chosen.1 chosen.2.1 chosen.2.2)

def receiptWritten (receipt:Selected binding n seed frame origin point):
 Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue (Lower.Value W n))) X s))):=
 some (selectedWrite receipt
  (fun path k _=>completed binding n seed frame origin point path k)
  (fun path k native=>NativeWriter.completed binding n seed frame
   (NativeWriter.backedPreimage binding n seed frame origin point path k native.val native.property.1).word))

def outputWrittenAt (outcome:ResidualDispositionOutcome (Indexed.face binding n seed frame origin)):
 OutputAt binding n seed frame origin outcome→
 Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue (Lower.Value W n))) X s))):=
 match outcome with
 | .unsound _ coordinate=>receiptWritten binding n seed frame origin coordinate
 | .faithful _ _ _ | .kernelResidual _ _ _ | .coverageResidual _ _ _=>fun _=>none

def generated:=outputWrittenAt binding n seed frame origin (disposition binding n seed frame origin)
 (output binding n seed frame origin)

theorem lookup_fee (path:List PUnit.{u+1}) (k:Nat):
 (profileResult binding n seed frame origin point path k).2.1.2.length=
 Coefficients.cost (actedWord binding n path point.relation):=profile_fee _ _ _ _ _ _ path k

def writerFee (path:List PUnit.{u+1}) (k:Nat):=
 (sourceTree binding n seed frame origin point path k).fold (fun source costs=>
  (Lower.SourceFamily.Foresight.Paid.paidTrace binding n ⟨frame,seed⟩ s (L.eventWord n source)).length+costs.sum)

def sourceFee (path:List PUnit.{u+1}) (k:Nat):=
 (sourceTree binding n seed frame origin point path k).fold (fun source costs=>
  remaining (Lower.SourceFamily.Foresight.Paid.expression (W:=W) (X:=X) n s (L.eventWord n source))+costs.sum)

theorem writer_fee (path:List PUnit.{u+1}) (k:Nat):writerFee binding n seed frame origin point path k=
 sourceFee binding n seed frame origin point path k:=by
 unfold writerFee sourceFee
 congr 1
 funext source costs
 exact congrArg (fun fee=>fee+costs.sum)
  (Lower.SourceFamily.Foresight.Paid.complete_fee binding n ⟨frame,seed⟩ s (L.eventWord n source))
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.Writer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
