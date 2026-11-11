import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.SourceOrigin

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
open private sourcePrefix_step from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.SourceOrigin
open private requestsFrom_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance intervalGroups (grade : Nat) : ∀ t, AddCommGroup (S.Value W grade t) := S.groups W grade
variable (factory : S.Factory W X s) (packet : S.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : ExecutionAt packet)
set_option quotPrecheck false in
local notation "events" => ((actedWords packet execution).map PresentedRelationEventAt.relation)
set_option quotPrecheck false in
local notation "sourcePrefix" => (sourceBlock factory packet execution).before
set_option quotPrecheck false in
local notation "decoder" => S.stockDecodedEnvironment (S.selected factory packet) (S.nativePacket factory packet).2.2.1
local notation "batch" => requests factory packet execution
local notation "point" => acted factory packet execution.stock execution.installed
set_option quotPrecheck false in
local notation "RequestEntry" =>
  F.Request (V := S.Value W (packet.1+1)) (X := packet.2.2.1.LowVar) (s := s)

/-- The full signed support of a source Step is an interval of the original receiver batch. -/
structure StepInterval (index : Fin (P.words execution.paid).length) where
  first : Nat
  count : Nat
  first_eq : first = (F.requestsFrom (sourcePrefix).length ((events).take index.val)).length
  count_eq : count = (Coefficients.sourceItems (point (execution.step index)).word).length
  requests_eq : ((batch).drop first).take count =
    F.requestsFrom (point (execution.step index)).before.length [.relation (point (execution.step index)).word]
  boundary_eq : ((((batch).drop first).take count).map (F.requestWord decoder)).sum =
    F.affine decoder (S.sourceWordAction packet (execution.step index).word)

/-- Select every request from the Step's actual ordinal before reading its affine boundary. -/
def stepInterval (index : Fin (P.words execution.paid).length) :
    StepInterval factory packet execution index := by
  let sourcePoint := point (execution.step index)
  let ordinal : Fin (events).length := Fin.cast (by simp only [List.length_map, actedWords]) index
  have exactWord : (execution.step index).word = (P.words execution.paid).get index :=
    ((P.stepOccurrence execution.paid index).transport_word execution.segment).trans
      (P.stepOccurrence_word execution.paid index)
  have oldRead : (P.words execution.paid)[index.val]? = some ((P.words execution.paid).get index) :=
    List.getElem?_eq_getElem index.isLt
  have eventRead : (events)[ordinal.val]? =
      some (.relation (S.sourceWordAction packet ((P.words execution.paid).get index))) := by
    change (((P.words execution.paid).map (S.sourceWordAction packet)).map PresentedRelationEventAt.relation)[index.val]? = _
    simp only [List.getElem?_map, oldRead, Option.map_some]
  have eventEq : (events).get ordinal = .relation sourcePoint.word :=
    (Option.some.inj ((List.getElem?_eq_getElem ordinal.isLt).symm.trans eventRead)).trans
      (congrArg (fun word => PresentedRelationEventAt.relation (S.sourceWordAction packet word)) exactWord.symm)
  have taken : ((events).take index.val).length = index.val :=
    List.length_take.trans (Nat.min_eq_left ordinal.isLt.le)
  have pointPosition : sourcePoint.before.length = (sourcePrefix).length + index.val :=
    (congrArg List.length (sourcePrefix_step factory packet execution index)).trans
      (List.length_append.trans (congrArg ((sourcePrefix).length + ·) taken))
  let prior : List RequestEntry := F.requestsFrom (sourcePrefix).length ((events).take index.val)
  let own : List RequestEntry := F.requestsFrom sourcePoint.before.length [.relation sourcePoint.word]
  let later : List RequestEntry := F.requestsFrom (sourcePoint.before.length+1) ((events).drop (index.val+1))
  have eventSplit : (events) = (events).take index.val ++ .relation sourcePoint.word :: (events).drop (index.val+1) :=
    (List.take_append_drop index.val (events)).symm.trans
      (congrArg ((events).take index.val ++ ·)
        ((List.drop_eq_getElem_cons ordinal.isLt).trans
          (congrArg (fun item => item :: (events).drop (index.val+1)) eventEq)))
  have requestSplit : batch = prior ++ own ++ later := by
    unfold requests
    refine (congrArg (F.requestsFrom (sourcePrefix).length) eventSplit).trans ?_
    rw [requestsFrom_append, taken, ← pointPosition]
    simp only [F.requestsFrom, List.append_nil, List.append_assoc, prior, own, later]
  have slice : ((batch).drop prior.length).take own.length = own :=
    (congrArg (fun (items : List RequestEntry) => (items.drop prior.length).take own.length) requestSplit).trans
      (by rw [List.append_assoc, List.drop_left, List.take_left])
  refine ⟨prior.length, own.length, rfl, ?_, slice, ?_⟩
  · change (F.requestsFrom sourcePoint.before.length [.relation sourcePoint.word]).length =
      (Coefficients.sourceItems sourcePoint.word).length
    simp only [F.requestsFrom, F.eventItems, List.append_nil, List.length_map]
  · refine (congrArg (fun (items : List RequestEntry) => (items.map (F.requestWord decoder)).sum) slice).trans ?_
    change ((F.requestsFrom sourcePoint.before.length [.relation sourcePoint.word]).map
      (F.requestWord decoder)).sum = F.affine decoder sourcePoint.word
    exact (F.relations_request_sum decoder sourcePoint.before.length [sourcePoint.word]).trans
      (congrArg (F.affine decoder) (List.sum_singleton))

/-- The backward request ordinal is the Step interval's original support slot. -/
theorem sourceRequestAt_interval_address (ordinal : Fin (batch).length)
    (origin : SourceRequestAt factory packet execution ordinal) :
    let group := stepInterval factory packet execution origin.sourceIndex
    ordinal.val = group.first + origin.supportIndex.val := by
  let group := stepInterval factory packet execution origin.sourceIndex
  let sourcePoint := point (execution.step origin.sourceIndex)
  let before := F.requestsFrom 0 (sourcePrefix)
  let ownBefore := F.requestsFrom (sourcePrefix).length ((events).take origin.sourceIndex.val)
  let entries := Coefficients.sourceItems sourcePoint.word
  have sourceBefore : F.requestsFrom 0 sourcePoint.before = before ++ ownBefore := by
    exact (congrArg (F.requestsFrom 0) (sourcePrefix_step factory packet execution origin.sourceIndex)).trans
      ((requestsFrom_append 0 (sourcePrefix) ((events).take origin.sourceIndex.val)).trans
        (congrArg (fun n => before ++ F.requestsFrom n ((events).take origin.sourceIndex.val))
          (Nat.zero_add (sourcePrefix).length)))
  have itemsLength : ((entries.take origin.supportIndex.val).map (F.sourceRequest sourcePoint)).length =
      origin.supportIndex.val :=
    (List.length_map _).trans (List.length_take.trans (Nat.min_eq_left origin.supportIndex.isLt.le))
  have ordinalLength : ((batch).take ordinal.val).length = ordinal.val :=
    List.length_take.trans (Nat.min_eq_left ordinal.isLt.le)
  have exactLeft : (F.relationPrefix sourcePoint origin.supportIndex).length =
      before.length + (group.first + origin.supportIndex.val) := by
    calc
      _ = (F.requestsFrom 0 sourcePoint.before).length +
          ((entries.take origin.supportIndex.val).map (F.sourceRequest sourcePoint)).length := List.length_append
      _ = (before.length + ownBefore.length) + origin.supportIndex.val :=
        congrArg₂ Nat.add ((congrArg List.length sourceBefore).trans List.length_append) itemsLength
      _ = before.length + (group.first + origin.supportIndex.val) :=
        (Nat.add_assoc _ _ _).trans (congrArg (fun n => before.length + (n + origin.supportIndex.val)) group.first_eq.symm)
  have exactRight : (before ++ (batch).take ordinal.val).length = before.length + ordinal.val :=
    List.length_append.trans (congrArg (before.length + ·) ordinalLength)
  exact Nat.add_left_cancel (exactRight.symm.trans ((congrArg List.length origin.prefix_eq).symm.trans exactLeft))

end ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
