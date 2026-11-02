import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionCode

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionEnvelope

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation AdmissionCode

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem sealing_survives_the_actual_next_stage
    (cursor : Cursor (lift base)) (protocol : Rule (lift base)) (rival : Opponent (lift base))
    (key : Fin base.sites) (sealed : ready base ((EventStep.seed cursor).frame.inbox key) = false) :
    ready base ((EventStep.seed (cursor.after protocol rival)).frame.inbox key) = false := by
  rw [EventStep.actual_next_state]
  exact feedback_cannot_reopen_a_sealed_key base _ _ _ key sealed

theorem activation_is_an_admitted_event (row : StageTrace.Record (code := lift base))
    (key : Fin base.sites) (owned : StageTrace.activation row = some key) :
    ∃ event, StageTransport.admission row = some event ∧ event.val = .activate key := by
  unfold StageTrace.activation at owned
  split at owned <;> try contradiction
  rename_i site event call
  split at owned <;> try contradiction
  rename_i kind
  cases Option.some.inj owned
  exact ⟨event, by simp only [StageTransport.admission, call, ControlExecution.admitted], kind⟩

theorem an_owned_activation_seals_a_non_rewritable_key
    (cursor : Cursor (lift base)) (protocol : Rule (lift base)) (rival : Opponent (lift base))
    (key : Fin base.sites) (owned : StageTrace.activation (StageTrace.material cursor protocol rival) = some key)
    (forbidden : mayRewrite base key = false) :
    ready base ((EventStep.seed (cursor.after protocol rival)).frame.inbox key) = false := by
  obtain ⟨event, admitted, kind⟩ := activation_is_an_admitted_event base _ key owned
  have live := (StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival key owned).1
  change (EventStep.seed cursor).remaining ≠ 0 at live
  change ControlExecution.admitted (lift base) (StageTrace.capture cursor protocol rival (EventStep.seed cursor)) = some event at admitted
  rw [← (StageTrace.material_is_the_actual_step cursor protocol rival).1]
  change ready base ((Reaction.Feedback.advance (lift base) (some protocol.work.val) _ (EventStep.seed cursor)).frame.inbox key) = false
  simp only [Reaction.Feedback.advance, decision, if_neg live, admitted, stepLocal, kind, Code.step]
  change ready base (pack base (ready base ((EventStep.seed cursor).frame.inbox key) && mayRewrite base key) _) = false
  rw [ready_pack, forbidden]
  exact Bool.and_false _

theorem issued_body_requires_an_open_latch
    (cursor : Cursor (lift base)) (protocol : Rule (lift base)) (rival : Opponent (lift base))
    (position : Nat) (body : StageBudget.Ballot (code := lift base))
    (made : StageBudget.issued vocabulary (StageTrace.material cursor protocol rival) position = some body) :
    ready base ((EventStep.seed cursor).frame.inbox body.key) = true := by
  obtain ⟨site, item, owned, present, _, _, _, _, key, _⟩ :=
    StageBudget.issued_has_an_owned_valid_paid_origin vocabulary _ position body made
  have word := (StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival site owned).2
  rw [key]
  by_cases available : ready base ((EventStep.seed cursor).frame.inbox site) = true
  · exact available
  · have closed : ready base ((EventStep.seed cursor).frame.inbox site) = false := by simpa using available
    have empty : (StageTrace.material cursor protocol rival).submitted = [] := by
      rw [word]
      simp only [Code.action, lift, closed, Bool.false_and, Bool.false_eq_true, if_false]
    have noItems : StageTrace.items (StageTrace.material cursor protocol rival) = [] := by
      unfold StageTrace.items
      rw [empty]
      rfl
    rw [noItems] at present
    simp at present

omit [DecidableEq Port] [DecidableEq Technology] in
theorem an_activation_submits_at_most_one_request (protocol : Rule (lift base))
    (key : Fin base.sites) (signal : Fin (lift base).signals) :
    ((lift base).action protocol.work.val key signal).length ≤ 1 := by
  have generated := (List.mem_pi _ _).mp protocol.work.property (key, signal) ((lift base).key_mem _)
  have bounded := ((mem_words_iff _ _ _).mp generated).1
  unfold Code.action
  split
  · exact bounded
  · simp

theorem an_issued_position_is_zero
    (cursor : Cursor (lift base)) (protocol : Rule (lift base)) (rival : Opponent (lift base))
    (position : Nat) (body : StageBudget.Ballot (code := lift base))
    (made : StageBudget.issued vocabulary (StageTrace.material cursor protocol rival) position = some body) : position = 0 := by
  obtain ⟨site, item, owned, present, _⟩ := StageBudget.issued_has_an_owned_valid_paid_origin vocabulary _ position body made
  obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp present
  have length := congrArg List.length ((lift base).law.inventory_requests_exact
    (StageTrace.material cursor protocol rival).before.current 0 (StageTrace.material cursor protocol rival).submitted)
  have exactLength : (StageTrace.items (StageTrace.material cursor protocol rival)).length =
      (StageTrace.material cursor protocol rival).submitted.length := by
        simpa only [StageTrace.items, RawLaw.rawItems, List.length_map] using length
  rw [exactLength] at bounded
  rw [(StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival site owned).2] at bounded
  have limit := an_activation_submits_at_most_one_request base protocol site ((EventStep.seed cursor).frame.inbox site)
  omega

theorem two_issued_bodies_of_one_activation_are_identical
    (cursor : Cursor (lift base)) (protocol : Rule (lift base)) (rival : Opponent (lift base))
    (first second : StageBudget.Ballot (code := lift base)) (a b : Nat)
    (one : StageBudget.issued vocabulary (StageTrace.material cursor protocol rival) a = some first)
    (two : StageBudget.issued vocabulary (StageTrace.material cursor protocol rival) b = some second) : first = second := by
  rw [an_issued_position_is_zero base vocabulary cursor protocol rival a first one] at one
  rw [an_issued_position_is_zero base vocabulary cursor protocol rival b second two] at two
  exact Option.some.inj (one.symm.trans two)

theorem a_sealed_key_has_no_later_issued_ballot
    (cursor : Cursor (lift base)) (stages : List (EventHistory.Stage (code := lift base)))
    (key : Fin base.sites) (sealed : ready base ((EventStep.seed cursor).frame.inbox key) = false)
    (body : StageBudget.Ballot (code := lift base)) (inside : body ∈ StageBudget.ledger vocabulary cursor stages) : body.key ≠ key := by
  induction stages generalizing cursor with
  | nil => simp [StageBudget.ledger, StageTrace.records] at inside
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    change body ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at inside
    rcases List.mem_append.mp inside with now | later
    · obtain ⟨position, _, made⟩ := List.mem_filterMap.mp now
      have available := issued_body_requires_an_open_latch base vocabulary cursor protocol rival position body made
      intro same
      rw [same, sealed] at available
      contradiction
    · exact ih (cursor.after protocol rival) (sealing_survives_the_actual_next_stage base cursor protocol rival key sealed) later

theorem a_non_rewritable_key_has_one_issued_body
    (cursor : Cursor (lift base)) (stages : List (EventHistory.Stage (code := lift base)))
    (first second : StageBudget.Ballot (code := lift base))
    (one : first ∈ StageBudget.ledger vocabulary cursor stages) (two : second ∈ StageBudget.ledger vocabulary cursor stages)
    (same : first.key = second.key) (forbidden : mayRewrite base first.key = false) : first = second := by
  induction stages generalizing cursor with
  | nil => simp [StageBudget.ledger, StageTrace.records] at one
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    change first ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at one
    change second ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at two
    rcases List.mem_append.mp one with firstNow | firstLater
    · obtain ⟨a, _, firstMade⟩ := List.mem_filterMap.mp firstNow
      rcases List.mem_append.mp two with secondNow | secondLater
      · obtain ⟨b, _, secondMade⟩ := List.mem_filterMap.mp secondNow
        exact two_issued_bodies_of_one_activation_are_identical base vocabulary cursor protocol rival first second a b firstMade secondMade
      · have owned := (StageBudget.issued_is_in_the_actual_installed_local_word vocabulary cursor [(protocol, rival)]
          (StageTrace.material cursor protocol rival) List.mem_cons_self a first firstMade).2.1
        have sealed := an_owned_activation_seals_a_non_rewritable_key base cursor protocol rival first.key owned forbidden
        exact False.elim ((a_sealed_key_has_no_later_issued_ballot base vocabulary (cursor.after protocol rival) tail first.key sealed second secondLater) same.symm)
    · rcases List.mem_append.mp two with secondNow | secondLater
      · obtain ⟨b, _, secondMade⟩ := List.mem_filterMap.mp secondNow
        have owned := (StageBudget.issued_is_in_the_actual_installed_local_word vocabulary cursor [(protocol, rival)]
          (StageTrace.material cursor protocol rival) List.mem_cons_self b second secondMade).2.1
        have sealed := an_owned_activation_seals_a_non_rewritable_key base cursor protocol rival second.key owned (same ▸ forbidden)
        exact False.elim ((a_sealed_key_has_no_later_issued_ballot base vocabulary (cursor.after protocol rival) tail second.key sealed first firstLater) same)
      · exact ih (cursor.after protocol rival) firstLater secondLater

theorem every_actual_equivocator_is_in_the_genesis_admission_budget
    (cursor : Cursor (lift base)) (stages : List (EventHistory.Stage (code := lift base)))
    (first second : StageBudget.Ballot (code := lift base))
    (one : first ∈ StageBudget.ledger vocabulary cursor stages) (two : second ∈ StageBudget.ledger vocabulary cursor stages)
    (same : first.key = second.key) (different : first.choice ≠ second.choice) : first.key ∈ affected base := by
  by_contra outside
  have forbidden : mayRewrite base first.key = false := by simpa [affected] using outside
  exact different (congrArg OwnedAttestation.BallotData.choice
    (a_non_rewritable_key_has_one_issued_body base vocabulary cursor stages first second one two same forbidden))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionEnvelope
