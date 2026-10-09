import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Renderer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Dispatch
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Tree
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Reader.Core
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Forecast
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState sourceHigh epochIndex)
end I
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Q
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev state := I.nativeState n data.2 data.1
local instance modelModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding (state n data) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (state n data) s 0)).module

def source := (I.sourceHigh binding n data.2 data.1).2.2.2.1 s
theorem source_projection : source binding n data=Lower.SourceFamily.Foresight.sourceMap binding (state n data) s 0 :=rfl
abbrev nativeFrame := Q.epoch data.1
abbrev nativeIndex := I.epochIndex n (nativeFrame n data)
abbrev sourceRaw := Reader.Core.raw binding n data.2 (nativeFrame n data) (nativeIndex n data)
abbrev face := Dispatch.face data.2 (nativeFrame n data) (nativeIndex n data).2 (source binding n data)
abbrev disposition := (face binding n data).settleWithResidual
def query := Dispatch.queryRaw data.2 (nativeFrame n data) (nativeIndex n data).2 (sourceRaw binding n data)
 (source binding n data) (disposition binding n data)
def event : Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n :=.generator (query binding n data).expression

def tree : RootedAccountedUnfolding (Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n) :=
 match disposition binding n data with
 | .kernelResidual sound _ point =>SourceHistoryCommon.seed (.zero (event binding n data))
  (.zero (.relation (Dispatch.kernelWord data.2 (nativeFrame n data) (nativeIndex n data).2
   (source binding n data) sound point).val))
 | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ =>.zero (event binding n data)

theorem source_event_present : event binding n data ∈ (tree binding n data).trace :=by
 unfold tree
 cases disposition binding n data with
 | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ =>exact List.mem_cons_self
 | kernelResidual _ _ _ =>exact (SourceHistoryCommon.parallel_left _ _ _).1 _ List.mem_cons_self

theorem scope_evaluation (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 (face binding n data).freeEvaluation word=SourceOperationLogic.q (source binding n data) word :=
 Dispatch.free_evaluation _ _ _ _ word

theorem rendered_word (word : Lower.SourceFamily.Foresight.Word binding (state n data) s 0) :
 SourceOperationLogic.q (source binding n data) (Finsupp.single (Coefficients.expression word) 1)=
 SourceOperationLogic.q (source binding n data) word :=by
 apply (SourceOperationLogic.q_eq_iff (source binding n data) _ _).mpr
 exact (LinearMap.mem_ker).mpr
  (((source binding n data).map_sub _ _).trans
   (sub_eq_zero.mpr (Rendering.rendered_source binding (state n data) s 0 word)))

theorem coverage_query_scope (sound : GeneratedRelationSoundnessAt (face binding n data))
 (obstruction : GeneratedCoverageResidualObstructionAt (face binding n data) sound)
 (point : GeneratedCoverageResidualCoordinateAt (face binding n data) sound) :
 SourceOperationLogic.q (source binding n data) (Finsupp.single
  (Dispatch.queryRaw data.2 (nativeFrame n data) (nativeIndex n data).2 (sourceRaw binding n data)
   (source binding n data) (.coverageResidual sound obstruction point)).expression 1)=point.representative :=
 (rendered_word binding n data (Dispatch.pointWord (source binding n data) point.representative)).trans
 (Dispatch.point_word (source binding n data) point.representative)

theorem query_environment : (query binding n data).environment=(sourceRaw binding n data).environment :=
 Dispatch.query_environment _ _ _ _ _ _


end Lower.SourceFamily.Foresight.Contextual.Forecast
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
