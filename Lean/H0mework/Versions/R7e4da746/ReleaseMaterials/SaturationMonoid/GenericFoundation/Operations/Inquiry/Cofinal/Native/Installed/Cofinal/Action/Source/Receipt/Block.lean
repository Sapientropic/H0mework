import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.ReceiptOccurrence
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations CofinalHistorySettlement
open ActualNativeRelationTransport (OccurrenceBlock)
open private requestsFrom_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

def executedTrace (decoder : Env V X) (items : List (Request (V := V) (X := X) (s := s))) :=
  RootedAccountedUnfolding.traceBranches (executionBranches decoder items)

private theorem executedTrace_append (decoder : Env V X)
    (first last : List (Request (V := V) (X := X) (s := s))) :
    executedTrace decoder (first ++ last) =
      executedTrace decoder first ++ executedTrace decoder last := by
  induction first with
  | nil => rfl
  | cons request rest previous =>
    let exposure := SourceOperationPaidRelations.exposure (receipt decoder request)
    change exposure.trace ++ executedTrace decoder (rest ++ last) =
      (exposure.trace ++ executedTrace decoder rest) ++ executedTrace decoder last
    rw [previous, List.append_assoc]

/-- Replay the original interval at its actual offset. Equal expressions retain separate receipts. -/
def writtenBlock (decoder : Env V X) (source : Inventory (V := V) (X := X) (s := s))
    (events : List (Event (V := V) (X := X) (s := s)))
    (block : OccurrenceBlock events source.trace) :
    OccurrenceBlock (executedTrace decoder (requestsFrom block.before.length events))
      (written decoder source).trace := by
  let before := requestsFrom 0 block.before
  let inside := requestsFrom block.before.length events
  let after := requestsFrom (block.before.length + events.length) block.after
  have split : requests source = before ++ inside ++ after := by
    unfold requests
    rw [block.trace_eq, requestsFrom_append, requestsFrom_append, List.length_append]
    simp only [Nat.zero_add, before, inside, after]
  refine ⟨source.trace ++ executedTrace decoder before, executedTrace decoder after, ?_⟩
  rw [written_trace, split]
  change source.trace ++ executedTrace decoder (before ++ inside ++ after) =
    (source.trace ++ executedTrace decoder before) ++ executedTrace decoder inside ++ executedTrace decoder after
  simp only [executedTrace_append, List.append_assoc]

/-- The signed contribution is read from the same request's complete paid trace. -/
def requestWord (decoder : Env V X) (item : Request (V := V) (X := X) (s := s)) :
    Formal ℤ V X s :=
  item.coefficient • (SourceOperationPaidRelations.words (receipt decoder item)).sum

private theorem relation_request_sum (decoder : Env V X) (position : Nat) (word : Formal ℤ V X s) :
    ((requestsFrom position [.relation word]).map (requestWord decoder)).sum = affine decoder word := by
  classical
  rw [affine_source_sum, Finsupp.linearCombination_apply]
  simp only [requestsFrom, eventItems, List.append_nil, List.map_map, Function.comp_def,
    Coefficients.sourceItems, requestWord, SourceOperationPaidRelations.paid_boundary,
    Trace.relation_boundary, Finsupp.sum]
  exact Finset.sum_map_toList _ _

/-- Keep each signed request until after execution, then recover the affine word of the whole interval. -/
theorem relations_request_sum (decoder : Env V X) (position : Nat) (words : List (Formal ℤ V X s)) :
    ((requestsFrom position (words.map PresentedRelationEventAt.relation)).map (requestWord decoder)).sum =
      affine decoder words.sum := by
  induction words generalizing position with
  | nil => simp only [List.map_nil, requestsFrom, List.sum_nil, map_zero]
  | cons word rest previous =>
    have split : requestsFrom position ((word::rest).map PresentedRelationEventAt.relation) =
        requestsFrom position [.relation word] ++
          requestsFrom (position+1) (rest.map PresentedRelationEventAt.relation) := by
      simp only [List.map_cons, requestsFrom, List.append_nil]
    rw [split, List.map_append, List.sum_append, relation_request_sum, previous, List.sum_cons, map_add]

end SourceInventoryExecutionFeed.ReceiptOccurrence

namespace ActualCofinalSourceAction.SourceReceiptOccurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
open ActualNativeRelationTransport (OccurrenceBlock)

namespace Batch
namespace F
export SourceInventoryExecutionFeed (Event Request requestsFrom written receipt affine)
export SourceInventoryExecutionFeed.ReceiptOccurrence (executedTrace requestWord writtenBlock relations_request_sum)
end F
namespace S
export ActualCofinalSourceAction (nativePacket selected sourceBorn bornStock sourceLiftEvent sourceWordAction source_word_action_relation)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.SF (Factory)
export ActualCofinalSourceAction.L (Value groups)
export ActualNativeRelationTransport.AS (stockScalar stockDecodedEnvironment)
end S
namespace P
export SourceOperationPaidRelations (words exposure events events_trace paid_boundary)
end P

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup (S.Value W grade target) :=
  S.groups W grade
variable (factory : S.Factory W X s) (packet : S.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : ExecutionAt packet)
set_option quotPrecheck false in
local notation "stock" => S.stockScalar (S.selected factory packet) (S.nativePacket factory packet).2.2.1
set_option quotPrecheck false in
local notation "decoder" => S.stockDecodedEnvironment (S.selected factory packet) (S.nativePacket factory packet).2.2.1
local notation "liftEvent" => S.sourceLiftEvent packet

def actedWords :=
  (P.words execution.paid).map (S.sourceWordAction packet)

/-- The old generator stays at the front; the chosen block starts at its first genuine relation Step. -/
def sourceBlock : OccurrenceBlock
    ((actedWords packet execution).map PresentedRelationEventAt.relation) (stock).trace := by
  let inherited := ActualNativeRelationTransport.SourceInventoryBlock.source factory packet execution.stock execution.installed
  let first := liftEvent (.generator execution.request.expression)
  refine ⟨inherited.before ++ execution.segment.before.map liftEvent ++ [first],
    execution.segment.after.map liftEvent ++ inherited.after, ?_⟩
  have exposure : (P.exposure execution.paid).trace.map liftEvent =
      first :: (actedWords packet execution).map PresentedRelationEventAt.relation := by
    change (.generator execution.request.expression ::
      RootedAccountedUnfolding.traceBranches (P.events execution.paid)).map liftEvent = _
    simp only [P.events_trace, List.map_cons, List.map_map, Function.comp_def, first,
      S.source_word_action_relation, actedWords]
  have mapped := congrArg (List.map liftEvent) execution.segment.trace_eq
  refine inherited.trace_eq.trans ((congrArg (fun chunk => inherited.before ++ chunk ++ inherited.after) mapped).trans ?_)
  simp only [List.map_append, exposure, List.append_assoc, List.nil_append, List.cons_append]

def requests :=
  F.requestsFrom (sourceBlock factory packet execution).before.length
    ((actedWords packet execution).map PresentedRelationEventAt.relation)

/-- The entire paid batch is a contiguous block of the original literal next inventory. -/
def nextBlock : OccurrenceBlock (F.executedTrace decoder (requests factory packet execution))
    (S.bornStock factory packet).trace :=
  F.writtenBlock decoder stock _ (sourceBlock factory packet execution)

/-- The exact requests in this same block pay the full acted boundary. -/
theorem nextBlock_boundary :
    ((requests factory packet execution).map (F.requestWord decoder)).sum =
      F.affine decoder (S.sourceWordAction packet
        (Finsupp.single execution.request.expression 1 -
          Finsupp.single (.const (execution.request.expression.eval execution.decoder)) 1)) := by
  have balance := F.relations_request_sum decoder (sourceBlock factory packet execution).before.length
    (actedWords packet execution)
  refine balance.trans ?_
  have source := (P.paid_boundary execution.paid).trans (execution.paid.relation_boundary (R := ℤ))
  exact congrArg (F.affine decoder)
    ((map_list_sum (S.sourceWordAction packet) (P.words execution.paid)).symm.trans
      (congrArg (S.sourceWordAction packet) source))

end Batch
end ActualCofinalSourceAction.SourceReceiptOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
