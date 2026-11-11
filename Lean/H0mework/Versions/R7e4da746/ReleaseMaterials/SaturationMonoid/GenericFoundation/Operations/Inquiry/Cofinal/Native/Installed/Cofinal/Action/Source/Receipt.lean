import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Relation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceReceiptOccurrence"

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.ReceiptOccurrence
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open private sourceRequestSplit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution
namespace P
export SourceOperationPaidRelations (exposure)
end P

variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}

private def executed (environment : Env V X) (items : List (Request (V := V) (X := X) (s := s))) :=
  RootedAccountedUnfolding.traceBranches (executionBranches environment items)

private theorem execution_split (environment : Env V X)
    (before after : List (Request (V := V) (X := X) (s := s)))
    (request : Request (V := V) (X := X) (s := s)) :
    executed environment (before ++ request :: after) =
      executed environment before ++ (P.exposure (receipt environment request)).trace ++
        executed environment after := by
  induction before with
  | nil => rfl
  | cons head tail previous =>
    let headTrace := (P.exposure (receipt environment head)).trace
    change headTrace ++ executed environment (tail ++ request :: after) =
      (headTrace ++ executed environment tail) ++ (P.exposure (receipt environment request)).trace ++
        executed environment after
    rw [previous]
    simp only [List.append_assoc]

/-- The exact request split selects its complete execution branch in the actual write. -/
def fromSplit (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s))
    (before after : List (Request (V := V) (X := X) (s := s)))
    (request : Request (V := V) (X := X) (s := s))
    (split : requests source = before ++ request :: after) :
    SourceInventoryTraceSegment (P.exposure (receipt environment request)) (written environment source) :=
  ⟨source.trace ++ executed environment before, executed environment after, by
    rw [written_trace, split]
    change source.trace ++ executed environment (before ++ request :: after) = _
    rw [execution_split]
    simp only [List.append_assoc]⟩

theorem fromSplit_before_length (environment : Env V X) (source : Inventory (V := V) (X := X) (s := s))
    (before after : List (Request (V := V) (X := X) (s := s)))
    (request : Request (V := V) (X := X) (s := s))
    (split : requests source = before ++ request :: after) :
    (fromSplit environment source before after request split).before.length =
      source.trace.length +
        (RootedAccountedUnfolding.traceBranches (executionBranches environment before)).length :=
  List.length_append

def relationPrefix {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : WordReceipt.RelationOccurrence source)
    (index : Fin (Coefficients.sourceItems occurrence.word).length) :
    List (Request (V := V) (X := X) (s := s)) :=
  requestsFrom 0 occurrence.before ++
    ((Coefficients.sourceItems occurrence.word).take index.val).map (WordReceipt.sourceRequest occurrence)

def fromRelationIndex (environment : Env V X)
    {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : WordReceipt.RelationOccurrence source)
    (index : Fin (Coefficients.sourceItems occurrence.word).length) :
    SourceInventoryTraceSegment
      (P.exposure (receipt environment
        (WordReceipt.sourceRequest occurrence ((Coefficients.sourceItems occurrence.word).get index))))
      (written environment source) :=
  let entries := Coefficients.sourceItems occurrence.word
  let item := entries.get index
  let split := sourceRequestSplit source occurrence ⟨item, List.get_mem entries index⟩
  fromSplit environment source split.1 split.2.1 (WordReceipt.sourceRequest occurrence item) split.2.2

theorem fromRelationIndex_before_length (environment : Env V X)
    {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : WordReceipt.RelationOccurrence source)
    (index : Fin (Coefficients.sourceItems occurrence.word).length) :
    (fromRelationIndex environment occurrence index).before.length =
      source.trace.length + (RootedAccountedUnfolding.traceBranches
        (executionBranches environment (relationPrefix occurrence index))).length := by
  classical
  let entries := Coefficients.sourceItems occurrence.word
  have nodup : entries.Nodup :=
    List.Nodup.map (fun _ _ equal => congrArg Prod.fst equal) (Finset.nodup_toList _)
  have offset : entries.idxOf (entries.get index) = index.val := List.get_idxOf nodup index
  unfold fromRelationIndex
  rw [fromSplit_before_length]
  change source.trace.length + (executed environment (requestsFrom 0 occurrence.before ++
    (entries.take (entries.idxOf (entries.get index))).map (WordReceipt.sourceRequest occurrence))).length =
      source.trace.length + (executed environment (relationPrefix occurrence index)).length
  rw [offset]
  rfl

end SourceInventoryExecutionFeed.ReceiptOccurrence

namespace ActualCofinalSourceAction.SourceReceiptOccurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace A
export ActualCofinalSourceAction
  (packetTransport nativePacket selected sourceBorn bornStock born_inventory)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.SF (Factory)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment stockScalar)
export ActualNativeRelationTransport (decoded_environment)
end A
namespace L
export ActualCofinalSourceAction.L (Value groups)
end L
namespace P
export SourceOperationPaidRelations
  (exposure words stepOccurrence stepOccurrence_word stepOccurrence_before_length paid_boundary)
end P
namespace Feed
export SourceInventoryExecutionFeed (Inventory Request receipt relationSpace executionBranches)
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence sourceRequest)
export SourceInventoryExecutionFeed.ReceiptOccurrence
  (fromRelationIndex relationPrefix fromRelationIndex_before_length)
end Feed
namespace Relation
export ActualNativeRelationTransport.SourceRelationOccurrence (source source_before_length)
end Relation

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) :
    AddCommGroup (L.Value W grade target) := L.groups W grade target

abbrev InventoryAt (packet : A.AdmissionPacket (W := W) (X := X) (s := s)) :=
  Feed.Inventory (V := L.Value W packet.1) (X := X) (s := s)

/-- An already executed request's trace and its exact position in the installed inventory. -/
structure ExecutionAt (packet : A.AdmissionPacket (W := W) (X := X) (s := s)) where
  stock : InventoryAt packet
  installed : packet.2.1.1.inventory = some stock
  decoder : Env (L.Value W packet.1) X
  decoder_source : packet.2.1.1.activeEnvironment = decoder
  request : Feed.Request (V := L.Value W packet.1) (X := X) (s := s)
  paid : Trace decoder request.expression (.const (request.expression.eval decoder))
  segment : SourceInventoryTraceSegment (P.exposure paid) stock

namespace ExecutionAt

variable {packet : A.AdmissionPacket (W := W) (X := X) (s := s)}

def step (execution : ExecutionAt packet) (index : Fin (P.words execution.paid).length) :
    Feed.RelationOccurrence execution.stock :=
  (P.stepOccurrence execution.paid index).transport execution.segment

theorem step_position (execution : ExecutionAt packet) (index : Fin (P.words execution.paid).length) :
    (execution.step index).before.length = execution.segment.before.length + (1 + index.val) :=
  ((P.stepOccurrence execution.paid index).transport_position execution.segment).trans
    (congrArg (execution.segment.before.length + ·) (P.stepOccurrence_before_length execution.paid index))

theorem boundary_written (execution : ExecutionAt packet) :
    Finsupp.single execution.request.expression 1 -
      Finsupp.single (.const (execution.request.expression.eval execution.decoder)) 1 ∈
        Feed.relationSpace execution.stock := by
  rw [← execution.paid.relation_boundary (R := ℤ), ← P.paid_boundary execution.paid]
  apply _root_.list_sum_mem
  intro word member
  obtain ⟨index, written⟩ := List.mem_iff_get.mp member
  let point := execution.step index
  have same : point.word = word :=
    ((P.stepOccurrence execution.paid index).transport_word execution.segment).trans
      ((P.stepOccurrence_word execution.paid index).trans written)
  apply Submodule.subset_span
  rw [← same, point.trace_eq]
  exact List.mem_append_right _ List.mem_cons_self

section Reindex

variable {Y Z : Sorts → Type u}
variable (original : A.AdmissionPacket (W := W) (X := Y) (s := s))
variable (target : A.AdmissionPacket (W := W) (X := Z) (s := s))
variable (language : Y = Z) (same : A.packetTransport language original = target)
variable (execution : ExecutionAt original)

def reindex : ExecutionAt target := by
  cases language
  cases same
  exact execution

theorem reindex_length :
    (P.words (reindex original target language same execution).paid).length =
      (P.words execution.paid).length := by
  cases language
  cases same
  rfl

theorem reindex_step (index : Fin (P.words execution.paid).length) :
    HEq ((reindex original target language same execution).step
      (Fin.cast (reindex_length original target language same execution).symm index)) (execution.step index) := by
  cases language
  cases same
  rfl

theorem reindex_positions :
    (reindex original target language same execution).request.position = execution.request.position ∧
      (reindex original target language same execution).segment.before.length = execution.segment.before.length := by
  cases language
  cases same
  exact ⟨rfl, rfl⟩

end Reindex

end ExecutionAt

section Native

variable (factory : A.Factory W X s)
variable (packet : A.AdmissionPacket (W := W) (X := X) (s := s))
variable (prior : InventoryAt packet) (present : packet.2.1.1.inventory = some prior)
variable (origin : Feed.RelationOccurrence prior)

abbrev acted := Relation.source factory packet prior present origin

abbrev SupportIndex :=
  Fin (Coefficients.sourceItems (acted factory packet prior present origin).word).length

set_option cleanup.letToHave false in
/-- Select the receiver request by the source relation's location and execute it in the actual decoder. -/
def atBirth (index : SupportIndex factory packet prior present origin) : ExecutionAt (A.sourceBorn factory packet) :=
  let selected := A.selected factory packet
  let native := (A.nativePacket factory packet).2.2.1
  let environment := A.stockDecodedEnvironment selected native
  let point := acted factory packet prior present origin
  let request := Feed.sourceRequest point ((Coefficients.sourceItems point.word).get index)
  ⟨A.bornStock factory packet, A.born_inventory factory packet, environment,
    A.decoded_environment selected native, request, Feed.receipt environment request,
    Feed.fromRelationIndex environment point index⟩

theorem atBirth_request_position (index : SupportIndex factory packet prior present origin) :
    (atBirth factory packet prior present origin index).request.position =
      (ActualNativeRelationTransport.SourceInventoryBlock.source factory packet prior present).before.length +
        origin.before.length :=
  Relation.source_before_length factory packet prior present origin

theorem atBirth_segment_position (index : SupportIndex factory packet prior present origin) :
    (atBirth factory packet prior present origin index).segment.before.length =
      let selected := A.selected factory packet
      let native := (A.nativePacket factory packet).2.2.1
      (A.stockScalar selected native).trace.length +
        (RootedAccountedUnfolding.traceBranches (Feed.executionBranches
          (A.stockDecodedEnvironment selected native)
          (Feed.relationPrefix (acted factory packet prior present origin) index))).length :=
  Feed.fromRelationIndex_before_length
    (A.stockDecodedEnvironment (A.selected factory packet) (A.nativePacket factory packet).2.2.1)
    (acted factory packet prior present origin) index

end Native
end ActualCofinalSourceAction.SourceReceiptOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
