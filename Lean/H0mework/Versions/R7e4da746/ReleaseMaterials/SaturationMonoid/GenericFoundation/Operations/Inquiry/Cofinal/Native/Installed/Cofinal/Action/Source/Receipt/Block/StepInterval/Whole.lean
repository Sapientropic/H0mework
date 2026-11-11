import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.StepInterval

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.ReceiptOccurrence
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open private executedTrace_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

/-- The original request list concatenates exactly its source-event groups. -/
theorem requestsFrom_grouped (start : Nat) (events : List (Event (V := V) (X := X) (s := s))) :
    (List.ofFn (fun i : Fin events.length => requestsFrom (start+i.val) [events.get i])).flatten =
      requestsFrom start events := by
  induction events generalizing start with
  | nil => rfl
  | cons head tail previous =>
    rw [List.ofFn_succ, List.flatten_cons]
    have shifted :
        (fun i : Fin tail.length => requestsFrom (start+i.succ.val) [(head::tail).get i.succ]) =
        (fun i : Fin tail.length => requestsFrom (start+1+i.val) [tail.get i]) := by
      funext i
      exact congrArg (fun n => requestsFrom n [tail.get i]) (by
        change start + (i.val + 1) = start + 1 + i.val
        omega)
    rw [shifted, previous]
    change (requestsFrom (start+0) [head]) ++ requestsFrom (start+1) tail = requestsFrom start (head :: tail)
    simp only [Nat.add_zero, requestsFrom, List.append_nil]

/-- Grouping executions preserves the original complete ordered inventory. -/
theorem executedTrace_grouped (decoder : Env V X)
    (groups : List (List (Request (V := V) (X := X) (s := s)))) :
    executedTrace decoder groups.flatten = (groups.map (executedTrace decoder)).flatten := by
  induction groups with
  | nil => rfl
  | cons group rest previous =>
    simp only [List.flatten_cons, List.map_cons, executedTrace_append, previous]

end SourceInventoryExecutionFeed.ReceiptOccurrence

namespace ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
open private sourcePrefix_step from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.SourceOrigin

namespace F
export SourceInventoryExecutionFeed.ReceiptOccurrence (requestsFrom_grouped executedTrace_grouped)
end F

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance groupedStepGroups (grade : Nat) : ∀ t, AddCommGroup (S.Value W grade t) := S.groups W grade
variable (factory : S.Factory W X s) (packet : S.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : ExecutionAt packet)
set_option quotPrecheck false in
local notation "events" => ((actedWords packet execution).map PresentedRelationEventAt.relation)
set_option quotPrecheck false in
local notation "start" => (sourceBlock factory packet execution).before.length
set_option quotPrecheck false in
local notation "decoder" => S.stockDecodedEnvironment (S.selected factory packet) (S.nativePacket factory packet).2.2.1
local notation "batch" => requests factory packet execution
set_option quotPrecheck false in
local notation "StepIndex" => Fin (P.words execution.paid).length
set_option quotPrecheck false in
local notation "RequestEntry" =>
  F.Request (V := S.Value W (packet.1+1)) (X := packet.2.2.1.LowVar) (s := s)

/-- Every source Step contributes its actual slice in the order of the original paid Trace. -/
def groupedRequestLists : List (List RequestEntry) :=
  List.ofFn fun index : StepIndex =>
    let interval := stepInterval factory packet execution index
    ((batch).drop interval.first).take interval.count

private theorem group_at_event (index : StepIndex) (present : index.val < (events).length) :
    let interval := stepInterval factory packet execution index
    ((batch).drop interval.first).take interval.count =
      F.requestsFrom (start+index.val) [(events).get ⟨index.val, present⟩] := by
  let interval := stepInterval factory packet execution index
  let sourcePoint := acted factory packet execution.stock execution.installed (execution.step index)
  have wordAt : (execution.step index).word = (P.words execution.paid).get index :=
    ((P.stepOccurrence execution.paid index).transport_word execution.segment).trans
      (P.stepOccurrence_word execution.paid index)
  have oldRead : (P.words execution.paid)[index.val]? = some ((P.words execution.paid).get index) :=
    List.getElem?_eq_getElem index.isLt
  have eventRead : (events)[index.val]? = some (.relation sourcePoint.word) := by
    change (((P.words execution.paid).map (S.sourceWordAction packet)).map
      PresentedRelationEventAt.relation)[index.val]? =
      some (.relation (S.sourceWordAction packet (execution.step index).word))
    simp only [List.getElem?_map, oldRead, Option.map_some, wordAt]
  have eventEq : (events).get ⟨index.val, present⟩ = .relation sourcePoint.word :=
    Option.some.inj ((List.getElem?_eq_getElem present).symm.trans eventRead)
  have taken : ((events).take index.val).length = index.val :=
    List.length_take.trans (Nat.min_eq_left present.le)
  have position : sourcePoint.before.length = start + index.val :=
    (congrArg List.length (sourcePrefix_step factory packet execution index)).trans
      (List.length_append.trans (congrArg (start + ·) taken))
  exact interval.requests_eq.trans
    (congrArg₂ F.requestsFrom position (congrArg List.singleton eventEq.symm))

/-- The Step slices partition the entire original batch, with empty slices kept at their own positions. -/
theorem grouped_requests : (groupedRequestLists factory packet execution).flatten = batch := by
  let groupedEvents := List.ofFn fun index : Fin (events).length =>
    F.requestsFrom (start+index.val) [(events).get index]
  have lengthEq : (events).length = (P.words execution.paid).length := by
    simp only [List.length_map, actedWords]
  have sameGroups : groupedRequestLists factory packet execution = groupedEvents := by
    apply List.ext_getElem
    · simpa only [groupedRequestLists, groupedEvents, List.length_ofFn] using lengthEq.symm
    · intro position inSteps inEvents
      have stepPresent : position < (P.words execution.paid).length := by
        simpa only [groupedRequestLists, List.length_ofFn] using inSteps
      have eventPresent : position < (events).length := by
        simpa only [groupedEvents, List.length_ofFn] using inEvents
      simp only [groupedRequestLists, groupedEvents, List.getElem_ofFn]
      exact group_at_event factory packet execution ⟨position, stepPresent⟩ eventPresent
  exact (congrArg List.flatten sameGroups).trans (F.requestsFrom_grouped start events)

/-- These are all executed events of the original next block, in their original order. -/
theorem grouped_executed_trace :
    ((groupedRequestLists factory packet execution).map (F.executedTrace decoder)).flatten =
      F.executedTrace decoder batch :=
  (F.executedTrace_grouped decoder _).symm.trans
    (congrArg (F.executedTrace decoder) (grouped_requests factory packet execution))

/-- The per-Step signed fold is the existing complete request boundary of that batch. -/
theorem grouped_request_boundary :
    ((groupedRequestLists factory packet execution).map
      (fun group => (group.map (F.requestWord decoder)).sum)).sum =
      ((batch).map (F.requestWord decoder)).sum := by
  let groups := groupedRequestLists factory packet execution
  calc
    _ = ((groups.flatten).map (F.requestWord decoder)).sum := by
      let weight := F.requestWord (s := s) decoder
      let weighted := groups.map (List.map weight)
      have nested : (groups.map (fun group => (group.map weight).sum)).sum =
          (weighted.map List.sum).sum := congrArg List.sum List.map_map.symm
      have flatten : weighted.flatten.sum = ((groups.flatten).map weight).sum :=
        congrArg List.sum List.map_flatten.symm
      exact nested.trans (List.sum_flatten.symm.trans flatten)
    _ = _ := congrArg (fun requests : List RequestEntry => (requests.map (F.requestWord decoder)).sum)
      (grouped_requests factory packet execution)

end ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
