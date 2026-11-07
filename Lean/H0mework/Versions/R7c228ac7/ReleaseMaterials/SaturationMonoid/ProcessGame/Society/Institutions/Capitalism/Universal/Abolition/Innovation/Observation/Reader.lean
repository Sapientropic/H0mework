import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open PublicFunction.Distributed

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (rule : Rule Party Good Port Technology Instrument)

def isOwnRequest (request : Request Party Good Port Technology Instrument) : Bool :=
  match request.operation with
  | .use bearer goods .contribution => decide
      (request.signer = rule.observer ∧ request.consents = [] ∧ request.purpose = rule.port ∧
        request.gates = [] ∧ bearer = rule.observer ∧ goods = rule.cost)
  | _ => false

theorem isOwnRequest_exact (request : Request Party Good Port Technology Instrument) :
    isOwnRequest rule request = true ↔ request = rule.request := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  cases operation with
  | use bearer goods use => cases use <;> simp [isOwnRequest, Rule.request]
  | _ => simp [isOwnRequest, Rule.request]

def isOwnRead : Compile.RawInput Party Good Port Technology Instrument → Bool
  | .primitive request => isOwnRequest rule request
  | .execute [request] => isOwnRequest rule request
  | _ => false

theorem isOwnRead_exact (raw : Compile.RawInput Party Good Port Technology Instrument) :
    isOwnRead rule raw = true ↔ raw = .primitive rule.request ∨ raw = .execute [rule.request] := by
  cases raw with
  | primitive request => simp [isOwnRead, isOwnRequest_exact]
  | execute word =>
      cases word with
      | nil => simp [isOwnRead]
      | cons request rest => cases rest <;> simp [isOwnRead, isOwnRequest_exact]
  | _ => simp [isOwnRead]

theorem the_original_request_is_recognized :
    isOwnRead rule (.primitive rule.request) = true := (isOwnRead_exact rule _).mpr (Or.inl rfl)

theorem its_actual_singleton_execution_is_recognized :
    isOwnRead rule (.execute [rule.request]) = true := (isOwnRead_exact rule _).mpr (Or.inr rfl)

def actualReadResult (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) :=
  Physical.Public.compile input (Before input depth count prefixLimit renewalLimit oldPast past) raw

theorem the_primitive_result_is_the_original_result
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    actualReadResult input depth count prefixLimit renewalLimit oldPast past (.primitive rule.request) =
      originalResult input depth count prefixLimit renewalLimit oldPast rule past := rfl

def observationAt (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) : Option (Recall.Notice rule.code) :=
  if isOwnRead rule raw then
    if (actualReadResult input depth count prefixLimit renewalLimit oldPast past raw).isAccepted then
      some (.sent rule.site (localSignal input depth count prefixLimit renewalLimit oldPast rule past)) else none
  else none

theorem every_generated_signal_has_its_original_self_paid_source
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) (notice : Recall.Notice rule.code)
    (observed : observationAt input depth count prefixLimit renewalLimit oldPast rule past raw = some notice) :
    (raw = .primitive rule.request ∨ raw = .execute [rule.request]) ∧
      (actualReadResult input depth count prefixLimit renewalLimit oldPast past raw).isAccepted = true ∧
      notice = .sent rule.site (localSignal input depth count prefixLimit renewalLimit oldPast rule past) := by
  unfold observationAt at observed
  split at observed
  · rename_i original
    split at observed
    · rename_i paid
      exact ⟨(isOwnRead_exact rule raw).mp original, paid, (Option.some.inj observed).symm⟩
    · contradiction
  · contradiction

/-- The index belongs to the original completed prefix. A non-observation
position cannot manufacture an observation failure. -/
def failureAtPosition (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (position : Fin past.length) :
    Option (Physical.Public.ResultAt input (Before input depth count prefixLimit renewalLimit oldPast (past.take position.val))
      (past.get position)) :=
  if isOwnRead rule (past.get position) then
    let result := actualReadResult input depth count prefixLimit renewalLimit oldPast (past.take position.val) (past.get position)
    match result with
    | .refused .. => some result
    | .accepted .. | .metadata _ => none
  else none

/-- Own submitted syntax is remembered as an attempt, never as an observed
result. Failed or unpaid reads add neither a signal nor an attempted code. -/
def localNoticeAt (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    Compile.RawInput Party Good Port Technology Instrument → Option (Recall.Notice rule.code)
  | .code submitted => some (.attempted submitted.requests)
  | raw => observationAt input depth count prefixLimit renewalLimit oldPast rule past raw

def localHistoryFrom (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    List (Compile.RawInput Party Good Port Technology Instrument) → List (Recall.Notice rule.code)
  | [] => []
  | raw :: remaining =>
      (localNoticeAt input depth count prefixLimit renewalLimit oldPast rule past raw).toList ++
        localHistoryFrom (past ++ [raw]) remaining

def localHistory (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  localHistoryFrom input depth count prefixLimit renewalLimit oldPast rule [] past

theorem retained_history_is_consumed_in_its_original_order
    (past first remaining : List (Compile.RawInput Party Good Port Technology Instrument)) :
    localHistoryFrom input depth count prefixLimit renewalLimit oldPast rule past (first ++ remaining) =
      localHistoryFrom input depth count prefixLimit renewalLimit oldPast rule past first ++
        localHistoryFrom input depth count prefixLimit renewalLimit oldPast rule (past ++ first) remaining := by
  induction first generalizing past with
  | nil => simp only [List.nil_append, localHistoryFrom, List.append_nil]
  | cons raw rest ih =>
      simp only [List.cons_append, localHistoryFrom, ih, List.append_assoc, List.nil_append]

theorem a_refused_original_read_keeps_the_entire_local_record
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (unpaid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = false) :
    localHistory input depth count prefixLimit renewalLimit oldPast rule (past ++ [.primitive rule.request]) =
      localHistory input depth count prefixLimit renewalLimit oldPast rule past := by
  rw [localHistory, retained_history_is_consumed_in_its_original_order]
  simp only [List.nil_append, localHistoryFrom, localNoticeAt, observationAt, the_original_request_is_recognized, ↓reduceIte,
    the_primitive_result_is_the_original_result, unpaid, Bool.false_eq_true,
    Option.toList_none, List.append_nil]
  rfl

theorem a_paid_original_read_adds_just_its_one_local_signal
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (paid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = true) :
    localHistory input depth count prefixLimit renewalLimit oldPast rule (past ++ [.primitive rule.request]) =
      localHistory input depth count prefixLimit renewalLimit oldPast rule past ++
        [.sent rule.site (localSignal input depth count prefixLimit renewalLimit oldPast rule past)] := by
  rw [localHistory, retained_history_is_consumed_in_its_original_order]
  simp only [List.nil_append, localHistoryFrom, localNoticeAt, observationAt, the_original_request_is_recognized, ↓reduceIte,
    the_primitive_result_is_the_original_result, paid, Option.toList_some, List.append_nil]
  rfl

theorem its_own_code_is_retained_only_as_its_original_attempt
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (word : RawEvent Party Good Port Technology Instrument) :
    localHistory input depth count prefixLimit renewalLimit oldPast rule (past ++ [.code ⟨word⟩]) =
      localHistory input depth count prefixLimit renewalLimit oldPast rule past ++ [.attempted word] := by
  rw [localHistory, retained_history_is_consumed_in_its_original_order]
  simp only [localHistoryFrom, localNoticeAt, Option.toList_some, List.append_nil]
  rfl

def recordAtCut (past : List (Compile.RawInput Party Good Port Technology Instrument)) (cut : Nat) :=
  localHistory input depth count prefixLimit renewalLimit oldPast rule (past.take cut)

theorem a_different_future_cannot_change_any_prior_local_record
    (past future : List (Compile.RawInput Party Good Port Technology Instrument)) :
    recordAtCut input depth count prefixLimit renewalLimit oldPast rule (past ++ future) past.length =
      localHistory input depth count prefixLimit renewalLimit oldPast rule past := by
  simp only [recordAtCut, List.take_left]

/-- This is an index inventory of existing input positions, not a receipt
registry. Each completed source position is considered exactly once. -/
def paidPositions (past : List (Compile.RawInput Party Good Port Technology Instrument)) : List (Fin past.length) :=
  (List.finRange past.length).filter fun position =>
    (observationAt input depth count prefixLimit renewalLimit oldPast rule
      (past.take position.val) (past.get position)).isSome

theorem every_original_read_position_is_considered_at_most_once
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    (paidPositions input depth count prefixLimit renewalLimit oldPast rule past).Nodup := by
  exact List.Nodup.filter _ (List.nodup_finRange past.length)

theorem the_number_of_paid_records_cannot_exceed_the_actual_prefix
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    (paidPositions input depth count prefixLimit renewalLimit oldPast rule past).length ≤ past.length := by
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

/-- The fixed programme receives only actual local notices. An attempted
code may make its next result `none`, yielding the original advance opcode. -/
abbrev Programme := List (Recall.Notice rule.code) → Option (RawEvent Party Good Port Technology Instrument)

def latestReading (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument) :
    List (Recall.Notice rule.code) → Option (RawEvent Party Good Port Technology Instrument)
  | [] => none
  | .sent _ signal :: _ => some (choose signal)
  | .attempted _ :: _ => none
  | .received _ _ :: remaining => latestReading choose remaining

/-- A new paid reading selects fresh syntax. Its own subsequent submission
is an acknowledgement, so a repeated read of the same prefix emits advance. -/
def programmeFromSensor (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument) : Programme rule :=
  fun record => latestReading rule choose record.reverse

omit [DecidableEq Port] in
theorem a_new_paid_signal_drives_the_fixed_rule
    (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument)
    (record : List (Recall.Notice rule.code)) (signal : Fin rule.code.signals) :
    programmeFromSensor rule choose (record ++ [.sent rule.site signal]) = some (choose signal) := by
  simp only [programmeFromSensor, List.reverse_append, List.reverse_singleton, List.singleton_append, latestReading]

omit [DecidableEq Port] in
theorem its_own_code_attempt_generates_the_next_advance
    (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument)
    (record : List (Recall.Notice rule.code)) (word : RawEvent Party Good Port Technology Instrument) :
    programmeFromSensor rule choose (record ++ [.attempted word]) = none := by
  simp only [programmeFromSensor, List.reverse_append, List.reverse_singleton, List.singleton_append, latestReading]

def proposalFromRecord (programme : Programme rule) (record : List (Recall.Notice rule.code)) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match programme record with
  | some word => .code ⟨word⟩
  | none => .advance

def proposal (programme : Programme rule)
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  proposalFromRecord rule programme (localHistory input depth count prefixLimit renewalLimit oldPast rule past)

theorem the_same_paid_local_record_and_own_attempts_emit_the_same_raw_proposal
    (programme : Programme rule)
    (first second : List (Compile.RawInput Party Good Port Technology Instrument))
    (same : localHistory input depth count prefixLimit renewalLimit oldPast rule first =
      localHistory input depth count prefixLimit renewalLimit oldPast rule second) :
    proposal input depth count prefixLimit renewalLimit oldPast rule programme first =
      proposal input depth count prefixLimit renewalLimit oldPast rule programme second := by
  exact congrArg (proposalFromRecord rule programme) same

theorem future_suffixes_cannot_change_the_old_raw_proposal
    (programme : Programme rule)
    (past firstFuture secondFuture : List (Compile.RawInput Party Good Port Technology Instrument)) :
    proposalFromRecord rule programme
        (recordAtCut input depth count prefixLimit renewalLimit oldPast rule (past ++ firstFuture) past.length) =
      proposalFromRecord rule programme
        (recordAtCut input depth count prefixLimit renewalLimit oldPast rule (past ++ secondFuture) past.length) := by
  rw [a_different_future_cannot_change_any_prior_local_record,
    a_different_future_cannot_change_any_prior_local_record]

/-- An attempt is known locally as syntax, including a refused read. It
never becomes a paid result merely because the protocol remembers it. -/
def hasOwnAttempt (past : List (Compile.RawInput Party Good Port Technology Instrument)) : Bool :=
  past.any fun raw => isOwnRead rule raw || match raw with | .code _ => true | _ => false

def scheduledProposal (programme : Programme rule)
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match programme (localHistory input depth count prefixLimit renewalLimit oldPast rule past) with
  | some word => .code ⟨word⟩
  | none => if hasOwnAttempt rule past then .advance else .primitive rule.request

theorem the_empty_sensor_record_actually_requests_its_own_observation
    (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument) :
    scheduledProposal input depth count prefixLimit renewalLimit oldPast rule (programmeFromSensor rule choose) [] =
      .primitive rule.request := rfl

theorem a_refused_first_observation_is_not_retried_or_learned
    (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument)
    (unpaid : (originalResult input depth count prefixLimit renewalLimit oldPast rule []).isAccepted = false) :
    localHistory input depth count prefixLimit renewalLimit oldPast rule [.primitive rule.request] = [] ∧
      scheduledProposal input depth count prefixLimit renewalLimit oldPast rule (programmeFromSensor rule choose)
        [.primitive rule.request] = .advance := by
  have unchanged := a_refused_original_read_keeps_the_entire_local_record input depth count prefixLimit renewalLimit oldPast rule [] unpaid
  change localHistory input depth count prefixLimit renewalLimit oldPast rule [.primitive rule.request] = [] at unchanged
  refine ⟨unchanged, ?_⟩
  simp only [scheduledProposal, unchanged, programmeFromSensor, List.reverse_nil, latestReading,
    hasOwnAttempt, List.any_cons, List.any_nil, the_original_request_is_recognized, Bool.true_or, ↓reduceIte]

def reader (programme : Programme rule) : Macro.Raw.Reader input depth count :=
  fun absolute _ => scheduledProposal input depth count prefixLimit renewalLimit oldPast rule programme
    (absolute.past.drop oldPast.length)

theorem the_reader_uses_no_financial_or_global_hidden_input
    (programme : Programme rule) (absolute : Physical.Cursor Party Good Port Technology Instrument)
    (first second : (Epoch.Finance.process input depth count).GeneratedState) :
    reader input depth count prefixLimit renewalLimit oldPast rule programme absolute first =
      reader input depth count prefixLimit renewalLimit oldPast rule programme absolute second := rfl

theorem the_reader_reads_the_literal_public_source_suffix
    (programme : Programme rule) (current : Physical.Cursor Party Good Port Technology Instrument)
    (account : (Epoch.Finance.process input depth count).GeneratedState) :
    reader input depth count prefixLimit renewalLimit oldPast rule programme
        (Physical.receive (Physical.Prefix.cursor (oldPast ++ current.past)) current.incoming) account =
      scheduledProposal input depth count prefixLimit renewalLimit oldPast rule programme current.past := by
  simp only [reader, Physical.receive, Physical.Prefix.past_readback, List.drop_left]

#print axioms a_refused_original_read_keeps_the_entire_local_record
#print axioms every_original_read_position_is_considered_at_most_once
#print axioms future_suffixes_cannot_change_the_old_raw_proposal
#print axioms the_reader_reads_the_literal_public_source_suffix

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation
