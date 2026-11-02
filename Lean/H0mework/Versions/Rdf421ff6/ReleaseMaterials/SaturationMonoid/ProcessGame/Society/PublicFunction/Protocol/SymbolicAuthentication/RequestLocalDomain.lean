import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalLocalDomain

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestLocalDomain

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def statements (row : StageTrace.Record (code := code)) :=
  (List.range row.submitted.length).filterMap (RequestAttestation.issued vocabulary row)

theorem statements_depend_only_on_actual_material_and_ownership
    (left right : StageTrace.Record (code := code))
    (cut : left.cursor.cut = right.cursor.cut) (before : left.before = right.before)
    (word : left.submitted = right.submitted) (owned : StageTrace.activation left = StageTrace.activation right) :
    statements vocabulary left = statements vocabulary right := by
  have items : StageTrace.items left = StageTrace.items right := by
    unfold StageTrace.items
    rw [before, word]
  have legacy : ∀ position, StageBudget.outcome vocabulary left position = StageBudget.outcome vocabulary right position := by
    intro position
    simp only [StageBudget.outcome, owned, items, OwnedAttestation.classify, cut]
  have issued : ∀ position, RequestAttestation.issued vocabulary left position = RequestAttestation.issued vocabulary right position := by
    intro position
    simp only [RequestAttestation.issued, RequestAttestation.outcome, legacy, items]
  simp only [statements, word, issued]

structure Entry where
  cursor : Cursor code
  ledger : List (RequestAttestation.Statement (code := code))

def initial (start : Cursor code) : Entry (code := code) := ⟨start, []⟩

def step (entry : Entry (code := code)) (rule : Rule code) (rival : Opponent code) : Entry (code := code) :=
  ⟨entry.cursor.after rule rival, entry.ledger ++ statements vocabulary (StageTrace.material entry.cursor rule rival)⟩

def run : Entry (code := code) → List (EventHistory.Stage (code := code)) → Entry (code := code)
  | entry, [] => entry
  | entry, (rule, rival) :: tail => run (step vocabulary entry rule rival) tail

theorem run_cursor (entry : Entry (code := code)) (stages : List (EventHistory.Stage (code := code))) :
    (run vocabulary entry stages).cursor = EventHistory.execute entry.cursor stages := by
  induction stages generalizing entry with
  | nil => rfl
  | cons stage tail ih => exact ih _

theorem run_ledger (entry : Entry (code := code)) (stages : List (EventHistory.Stage (code := code))) :
    (run vocabulary entry stages).ledger = entry.ledger ++ RequestAttestation.ledger vocabulary entry.cursor stages := by
  induction stages generalizing entry with
  | nil => simp [run, RequestAttestation.ledger, StageTrace.records]
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    rw [run, ih]
    simp only [step, RequestAttestation.ledger, StageTrace.records, List.flatMap_cons, statements, List.append_assoc]

def Related (left right : Entry (code := code)) : Prop :=
  EventStep.Matches left.cursor right.cursor ∧ left.ledger = right.ledger

theorem a_compact_reply_retains_the_complete_authentication_ledger
    (left right : Entry (code := code)) (same : Related left right)
    (rule : Rule code) (rival : Opponent code) :
    Related (step vocabulary left rule (EventStep.fixed (CausalLocalDomain.chosen left.cursor right.cursor rival)))
      (step vocabulary right rule rival) := by
  have next := CausalLocalDomain.a_compact_reply_preserves_the_entire_actual_completed_prefix rule left.cursor right.cursor same.1 rival
  have word : (StageTrace.material left.cursor rule (EventStep.fixed (CausalLocalDomain.chosen left.cursor right.cursor rival))).submitted =
      (StageTrace.material right.cursor rule rival).submitted := by
    have histories := congrArg (fun state : State code => state.history) next.state
    rw [EventStep.actual_next_state, EventStep.actual_next_state] at histories
    simp only [history_keeps_every_actual_word] at histories
    have before := congrArg (fun state : State code => state.history) same.1.state
    rw [before] at histories
    have words := List.singleton_inj.mp (List.append_cancel_left histories)
    exact (StageTrace.material_is_the_actual_step _ _ _).2.trans
      (words.trans (StageTrace.material_is_the_actual_step _ _ _).2.symm)
  have owned : StageTrace.activation
      (StageTrace.material left.cursor rule (EventStep.fixed (CausalLocalDomain.chosen left.cursor right.cursor rival))) =
      StageTrace.activation (StageTrace.material right.cursor rule rival) := by
    by_cases stopped : (EventStep.seed right.cursor).remaining = 0
    · simp only [StageTrace.activation, StageTrace.material, StageTrace.capture, same.1.state, if_pos stopped]
    · simp only [StageTrace.activation, StageTrace.material, StageTrace.capture, same.1.state, same.1.ownerStart, if_neg stopped]
      cases owner : Distributed.Recall.Information.Agency.ownerAt code right.cursor.ownerStart
        (EventStep.seed right.cursor).history.length <;> rfl
  refine ⟨next, ?_⟩
  change left.ledger ++ _ = right.ledger ++ _
  rw [same.2]
  exact congrArg _ (statements_depend_only_on_actual_material_and_ownership vocabulary _ _ same.1.cut same.1.state word owned)

def advance (rule : Rule code) (domain : List (Entry (code := code))) :=
  domain.flatMap fun entry => (CausalLocalDomain.replies entry.cursor).map fun reply => step vocabulary entry rule (EventStep.fixed reply)

def history : List (Entry (code := code)) → List (Rule code) → List (Entry (code := code))
  | domain, [] => domain
  | domain, rule :: tail => history (advance vocabulary rule domain) tail

theorem every_adaptive_actual_trace_has_a_generated_authenticated_representative
    (domain : List (Entry (code := code))) (left right : Entry (code := code))
    (inside : left ∈ domain) (same : Related left right)
    (stages : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ history vocabulary domain (stages.map Prod.fst), Related representative (run vocabulary right stages) := by
  induction stages generalizing domain left right with
  | nil => exact ⟨left, inside, same⟩
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    have admitted : CausalLocalDomain.chosen left.cursor right.cursor rival ∈ CausalLocalDomain.replies left.cursor := by
      unfold CausalLocalDomain.chosen CausalLocalDomain.replies
      split
      · simp
      · exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨EventStep.selected right.cursor rival, every_move_is_generated code _, rfl⟩)
    have generated : step vocabulary left rule (EventStep.fixed (CausalLocalDomain.chosen left.cursor right.cursor rival)) ∈ advance vocabulary rule domain :=
      List.mem_flatMap.mpr ⟨left, inside, List.mem_map.mpr ⟨_, admitted, rfl⟩⟩
    exact ih _ _ _ generated (a_compact_reply_retains_the_complete_authentication_ledger vocabulary left right same rule rival)

def domain (start : Cursor code) (installed : List (Rule code)) := history vocabulary [initial start] installed

theorem actual_prefix_coverage (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ domain vocabulary start (stages.map Prod.fst),
      EventStep.Matches representative.cursor (EventHistory.execute start stages) ∧
      representative.ledger = RequestAttestation.ledger vocabulary start stages := by
  obtain ⟨representative, inside, same, ledger⟩ :=
    every_adaptive_actual_trace_has_a_generated_authenticated_representative vocabulary [initial start] (initial start) (initial start)
      (List.mem_singleton_self _) ⟨EventStep.matches_self _, rfl⟩ stages
  refine ⟨representative, inside, ?_, ?_⟩
  · simpa only [run_cursor, initial] using same
  · simpa only [run_ledger, initial, List.nil_append] using ledger

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestLocalDomain
