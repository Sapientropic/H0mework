import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePrefix

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code) (pastStages future : List (EventHistory.Stage (code := code)))

theorem record_at (index : Nat) (bounded : index < pastStages.length) :
    (StageTrace.records cursor (pastStages ++ future))[index]? = (StageTrace.records cursor pastStages)[index]? := by
  rw [StageQueue.records_append, List.getElem?_append_left]
  simpa only [StageTrace.record_count] using bounded

theorem records_before (index : Nat) (bounded : index ≤ pastStages.length) :
    (StageTrace.records cursor (pastStages ++ future)).take index = (StageTrace.records cursor pastStages).take index := by
  rw [StageQueue.records_append, List.take_append_of_le_length]
  simpa only [StageTrace.record_count] using bounded

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code))

theorem issued_at (index : Nat) (bounded : index < pastStages.length) :
    StageTransport.issuedAt vocabulary encoding cursor (pastStages ++ future) index =
      StageTransport.issuedAt vocabulary encoding cursor pastStages index := by
  simp only [StageTransport.issuedAt, record_at cursor pastStages future index bounded,
    records_before cursor pastStages future index (Nat.le_of_lt bounded)]

theorem incoming_at (index : Nat) (bounded : index < pastStages.length) :
    StageReception.incoming vocabulary encoding cursor (pastStages ++ future) index =
      StageReception.incoming vocabulary encoding cursor pastStages index := by
  have earlier : (List.range index).filterMap (StageTransport.issuedAt vocabulary encoding cursor (pastStages ++ future)) =
      (List.range index).filterMap (StageTransport.issuedAt vocabulary encoding cursor pastStages) := by
    apply List.filterMap_congr
    intro earlier inside
    exact issued_at cursor pastStages future vocabulary encoding earlier (by have prior := List.mem_range.mp inside; omega)
  simp only [StageReception.incoming, record_at cursor pastStages future index bounded, earlier]

theorem incoming_has_a_prior_actual_issue (index : Nat) (wire : StageTransport.Wire (code := code))
    (incoming : StageReception.incoming vocabulary encoding cursor pastStages index = some wire) :
    ∃ earlier < index, StageTransport.issuedAt vocabulary encoding cursor pastStages earlier = some wire := by
  unfold StageReception.incoming at incoming
  split at incoming <;> try contradiction
  split at incoming <;> try contradiction
  split at incoming <;> try contradiction
  obtain ⟨earlier, inside, actual⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some incoming)
  exact ⟨earlier, List.mem_range.mp inside, actual⟩

theorem incoming_is_authenticated (index : Nat) (bounded : index ≤ pastStages.length)
    (wire : StageTransport.Wire (code := code))
    (incoming : StageReception.incoming vocabulary encoding cursor pastStages index = some wire) :
    StageTransport.verify vocabulary encoding cursor pastStages wire = true := by
  obtain ⟨earlier, prior, actual⟩ := incoming_has_a_prior_actual_issue cursor pastStages vocabulary encoding index wire incoming
  exact decide_eq_true (List.mem_filterMap.mpr ⟨earlier, List.mem_range.mpr (by omega), actual⟩)

variable (law : StageReception.Law code)

theorem receive_at (receiver : Fin code.sites) (index : Nat) (bounded : index < pastStages.length)
    (previous : StageReception.Receiver (code := code)) :
    StageReception.receive vocabulary encoding law cursor (pastStages ++ future) receiver index previous =
      StageReception.receive vocabulary encoding law cursor pastStages receiver index previous := by
  simp only [StageReception.receive, record_at cursor pastStages future index bounded,
    incoming_at cursor pastStages future vocabulary encoding index bounded]
  cases actual : (StageTrace.records cursor pastStages)[index]? with
  | none => rfl
  | some row =>
    cases incoming : StageReception.incoming vocabulary encoding cursor pastStages index with
    | none => rfl
    | some wire =>
      have oldAuth := incoming_is_authenticated cursor pastStages vocabulary encoding index (Nat.le_of_lt bounded) wire incoming
      have nextAuth := incoming_is_authenticated cursor (pastStages ++ future) vocabulary encoding index
        (by simp only [List.length_append]; omega) wire
        ((incoming_at cursor pastStages future vocabulary encoding index bounded).trans incoming)
      simp only [StageReception.check, oldAuth, nextAuth]

theorem run_at (receiver : Fin code.sites) (count : Nat) (bounded : count ≤ pastStages.length) :
    StageReception.run vocabulary encoding law cursor (pastStages ++ future) receiver count =
      StageReception.run vocabulary encoding law cursor pastStages receiver count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [StageReception.run, receive_at cursor pastStages future vocabulary encoding law receiver count (by omega), ih (by omega)]

theorem receipts_survive_actual_extension (receiver : Fin code.sites) :
    (StageReception.run vocabulary encoding law cursor pastStages receiver pastStages.length).receipts <+:
      (StageReception.run vocabulary encoding law cursor (pastStages ++ future) receiver (pastStages ++ future).length).receipts := by
  rw [← run_at cursor pastStages future vocabulary encoding law receiver pastStages.length (Nat.le_refl _)]
  exact StageQueueProgress.receipts_are_preserved vocabulary encoding law cursor (pastStages ++ future) receiver _ _
    (by simp only [List.length_append]; omega)

theorem issued_at_take (index : Nat) (bounded : index < pastStages.length) :
    StageTransport.issuedAt vocabulary encoding cursor (pastStages.take (index + 1)) index =
      StageTransport.issuedAt vocabulary encoding cursor pastStages index := by
  have prior := issued_at cursor (pastStages.take (index + 1)) (pastStages.drop (index + 1)) vocabulary encoding index
    (by simp only [List.length_take]; omega)
  simpa only [List.take_append_drop] using prior.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePrefix
