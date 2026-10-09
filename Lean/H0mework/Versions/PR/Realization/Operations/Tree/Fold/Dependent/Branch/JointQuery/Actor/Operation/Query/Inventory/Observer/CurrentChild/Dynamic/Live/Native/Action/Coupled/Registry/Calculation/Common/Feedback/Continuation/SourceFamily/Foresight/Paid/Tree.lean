import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Fold
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Paid.Ledger

variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance groups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev SourceEvent := PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)
def eventWord : SourceEvent (W:=W) (X:=X) (s:=s) n → Lower.SourceFamily.Foresight.Paid.Word (W:=W) (X:=X) n s
 | .generator expression => Finsupp.single expression 1
 | .relation word => word
def rawEvent : SourceEvent (W:=W) (X:=X) (s:=s) n := .generator
 (Lower.SourceFamily.Foresight.Update.Q.query data.1
 (Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.factory (s:=s) binding) n data.2)).raw.expression
def sourceTreeAt (rootExpression : Expr (PairValue (Lower.Value W n)) X s) :
 RootedAccountedUnfolding (SourceEvent (W:=W) (X:=X) (s:=s) n) :=
 match data.1.pairInventory with
 | none => RootedAccountedUnfolding.zero (.generator rootExpression)
 | some history => SourceHistoryCommon.seed (RootedAccountedUnfolding.zero (.generator rootExpression)) history

def sourceTree : RootedAccountedUnfolding (SourceEvent (W:=W) (X:=X) (s:=s) n) :=
 sourceTreeAt n data
  (Lower.SourceFamily.Foresight.Update.Q.query data.1
   (Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.factory (s:=s) binding) n data.2)).raw.expression

theorem source_at_root (rootExpression : Expr (PairValue (Lower.Value W n)) X s) :
 (.generator rootExpression : SourceEvent (W:=W) (X:=X) (s:=s) n) ∈ (sourceTreeAt n data rootExpression).trace := by
 unfold sourceTreeAt
 cases data.1.pairInventory with
 | none => exact List.mem_cons_self
 | some history => exact (SourceHistoryCommon.parallel_left _ _ _).1 _ List.mem_cons_self

theorem source_at_inventory (rootExpression : Expr (PairValue (Lower.Value W n)) X s)
 (history : RootedAccountedUnfolding (SourceEvent (W:=W) (X:=X) (s:=s) n))
 (actual : data.1.pairInventory=some history) (event) (present : event ∈ history.trace) :
 event ∈ (sourceTreeAt n data rootExpression).trace := by
 unfold sourceTreeAt
 rw [actual]
 exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

def writeEvent (event : SourceEvent (W:=W) (X:=X) (s:=s) n) :=
 Lower.SourceFamily.Foresight.Paid.writtenAt binding n data (eventWord n event)
def generated := run (writeEvent binding n data) (sourceTree binding n data)
def extraPair := some (T.preserve
 ((Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1) (generated binding n data))

theorem source_raw_present : rawEvent binding n data ∈ (sourceTree binding n data).trace := by
 unfold sourceTree sourceTreeAt
 cases data.1.pairInventory with
 | none => exact List.mem_cons_self
 | some history => exact (SourceHistoryCommon.parallel_left _ _ _).1 _ List.mem_cons_self

theorem source_inventory_present (history : RootedAccountedUnfolding (SourceEvent (W:=W) (X:=X) (s:=s) n))
 (actual : data.1.pairInventory=some history) (event) (present : event ∈ history.trace) :
 event ∈ (sourceTree binding n data).trace := by
 unfold sourceTree sourceTreeAt
 rw [actual]
 exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem generated_keeps_paid (source : SourceEvent (W:=W) (X:=X) (s:=s) n)
 (present : source ∈ (sourceTree binding n data).trace) (event) (paid : event ∈ (writeEvent binding n data source).trace) :
 event ∈ (generated binding n data).trace := run_contains _ _ source present event paid

theorem extra_pair_keeps_paid (source : SourceEvent (W:=W) (X:=X) (s:=s) n)
 (present : source ∈ (sourceTree binding n data).trace) (event) (paid : event ∈ (writeEvent binding n data source).trace) :
 event ∈ ((extraPair binding n data).getD (generated binding n data)).trace := by
 have generatedFound := generated_keeps_paid binding n data source present event paid
 unfold extraPair T.preserve
 cases (Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1 with
 | none => exact generatedFound
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event generatedFound

def actualFee := (sourceTree binding n data).fold (fun source costs =>
 (Lower.SourceFamily.Foresight.Paid.paidTrace binding n data s (eventWord n source)).length+costs.sum)
def sourceFee := (sourceTree binding n data).fold (fun source costs =>
 remaining (Lower.SourceFamily.Foresight.Paid.expression (W:=W) (X:=X) n s (eventWord n source))+costs.sum)
theorem fee_source : actualFee binding n data=sourceFee binding n data := by
 unfold actualFee sourceFee
 congr 1
 funext source costs
 exact congrArg (fun fee => fee+costs.sum) (Lower.SourceFamily.Foresight.Paid.complete_fee binding n data s (eventWord n source))
end Lower.SourceFamily.Foresight.Paid.Ledger
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
