import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (original : Code Party Good Port Technology Instrument)

/-- An executable extension changes the finite language, retaining the actual
law, task and local information architecture. Its continuation starts at the
saved feedback state, not at the language enumerator's empty start frame. -/
structure Supply where
  actions : List (Request Party Good Port Technology Instrument)
  actionLimit : Nat
  histories : List (RawEvent Party Good Port Technology Instrument)
  historyLimit : Nat
  events : Events original
  eventLimit : Nat

abbrev code (supply : Supply original) : Code Party Good Port Technology Instrument :=
  {original with
    actions := original.actions ++ supply.actions
    actionLimit := max original.actionLimit supply.actionLimit
    historyAlphabet := original.historyAlphabet ++ supply.histories
    historyLimit := max original.historyLimit supply.historyLimit
    eventAlphabet := original.eventAlphabet ++ supply.events
    eventLimit := max original.eventLimit supply.eventLimit}

variable (supply : Supply original)

def packet (old : original.Packet) : (code original supply).Packet :=
  ⟨old.sender, old.recipient, old.signal, old.sentAfter⟩

def forgetPacket (new : (code original supply).Packet) : original.Packet :=
  ⟨new.sender, new.recipient, new.signal, new.sentAfter⟩

def frame (old : original.Frame) : (code original supply).Frame :=
  ⟨old.word, old.sent.map (packet original supply), old.inbox, old.localLegal⟩

def forgetFrame (new : (code original supply).Frame) : original.Frame :=
  ⟨new.word, new.sent.map (forgetPacket original supply), new.inbox, new.localLegal⟩

@[simp] theorem forget_frame (old : original.Frame) :
    forgetFrame original supply (frame original supply old) = old := by
  cases old
  simp only [forgetFrame, frame, List.map_map]
  have identity : forgetPacket original supply ∘ packet original supply = id := by
    funext p; cases p; rfl
  simp only [identity, List.map_id]

def state (old : State original) : State (code original supply) :=
  ⟨old.current, old.history, old.past, frame original supply old.frame, old.remaining⟩

def opponent (old : Opponent original) : Opponent (code original supply) :=
  fun history past current => (old history past (forgetFrame original supply current)).map
    (fun chosen => ⟨chosen.val, List.mem_append_left _ chosen.property⟩)

def input (old : Input original) : Input (code original supply) :=
  ⟨opponent original supply old.opponent, old.budget⟩

theorem all_original_policies_remain_generated (policy : original.Policy)
    (generated : policy ∈ original.policies) : policy ∈ (code original supply).policies := by
  apply (code original supply).every_local_policy_is_enumerated
  intro key inside
  obtain ⟨bounded, supported⟩ := (mem_words_iff _ _ _).mp
    ((List.mem_pi _ _).mp generated key inside)
  exact (mem_words_iff _ _ _).mpr ⟨bounded.trans (Nat.le_max_left _ _),
    fun request member => List.mem_append_left _ (supported request member)⟩

theorem history_legality_is_unchanged (current : RawCurrent Party Good Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument)) :
    (code original supply).historyLegal current past = original.historyLegal current past := by
  induction past generalizing current with
  | nil => rfl
  | cons head tail ih => simp only [Code.historyLegal, code, ih]

theorem all_original_histories_remain_generated
    (past : List (RawEvent Party Good Port Technology Instrument)) (generated : past ∈ original.histories) :
    past ∈ (code original supply).histories := by
  obtain ⟨hidden, member, rfl⟩ := List.mem_map.mp generated
  obtain ⟨inside, legal⟩ := List.mem_filter.mp member
  obtain ⟨bounded, supported⟩ := (mem_sequences_iff _ _ _).mp inside
  apply List.mem_map.mpr
  refine ⟨hidden, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact (mem_sequences_iff _ _ _).mpr ⟨bounded.trans (Nat.le_max_left _ _),
      fun word member => List.mem_append_left _ (supported word member)⟩
  · rw [history_legality_is_unchanged]
    exact legal

theorem all_original_scripts_remain_generated (events : Events original)
    (generated : events ∈ original.scripts) : events ∈ (code original supply).scripts := by
  obtain ⟨inside, eligible⟩ := List.mem_filter.mp generated
  obtain ⟨bounded, supported⟩ := (mem_sequences_iff _ _ _).mp inside
  exact List.mem_filter.mpr ⟨(mem_sequences_iff _ _ _).mpr
    ⟨bounded.trans (Nat.le_max_left _ _), fun event member => List.mem_append_left _ (supported event member)⟩,
    eligible⟩

theorem all_original_scenarios_remain_generated (scenario : original.Scenario)
    (generated : scenario ∈ original.scenarios) : scenario ∈ (code original supply).scenarios := by
  obtain ⟨history, events⟩ := List.mem_product.mp generated
  exact List.mem_product.mpr ⟨all_original_histories_remain_generated original supply _ history,
    all_original_scripts_remain_generated original supply _ events⟩

theorem step_preserves_the_actual_frame (policy : original.Policy)
    (current : RawCurrent Party Good Technology Instrument) (old : original.Frame)
    (event : Event Party Good Port Technology Instrument original.sites) :
    (code original supply).step policy current (frame original supply old) event =
      frame original supply (original.step policy current old event) := by
  cases event with
  | adversary request => rfl
  | send sender recipient =>
    simp only [Code.step, Code.rawAt, frame, Code.snapshot]
    congr 1
    let sent : original.Packet := ⟨sender, recipient,
      original.readLocal sender (original.snapshot sender (original.rawAt current old)), old.word.length⟩
    have mapped (paid : Bool) :
        (if paid then old.sent.map (packet original supply) ++ [packet original supply sent]
          else old.sent.map (packet original supply)) =
        (if paid then old.sent ++ [sent] else old.sent).map (packet original supply) := by
      cases paid <;> simp
    exact mapped _
  | deliver address =>
    simp only [Code.step, Code.rawAt, frame, List.getElem?_map]
    cases present : old.sent[address]? with
    | none => rfl
    | some p => rfl
  | activate site => rfl

theorem decision_preserves_the_same_opponent (oldInput : Input original) (old : State original) :
    decision (code original supply) (input original supply oldInput) (state original supply old) =
      (decision original oldInput old).map
        (fun chosen => ⟨chosen.val, List.mem_append_left _ chosen.property⟩) := by
  simp only [decision, input, state, opponent, forget_frame]
  split <;> rfl

theorem word_preserves_the_actual_request (policy : Option original.Policy)
    (oldInput : Input original) (old : State original) :
    word (code original supply) policy (input original supply oldInput) (state original supply old) =
      word original policy oldInput old := by
  simp only [word, decision_preserves_the_same_opponent]
  cases policy with
  | none => rfl
  | some policy =>
    cases choice : decision original oldInput old with
    | none => rfl
    | some chosen =>
      change ((code original supply).step policy old.current
        (frame original supply {old.frame with word := []}) chosen.val).word = _
      rw [step_preserves_the_actual_frame]
      rfl

theorem advance_preserves_the_whole_actual_state (policy : Option original.Policy)
    (oldInput : Input original) (old : State original) :
    advance (code original supply) policy (input original supply oldInput) (state original supply old) =
      state original supply (advance original policy oldInput old) := by
  simp only [advance, word_preserves_the_actual_request, decision_preserves_the_same_opponent]
  cases policy with
  | none => rfl
  | some policy =>
    cases choice : decision original oldInput old with
    | none => rfl
    | some chosen =>
      simp only [Option.map_some, stepLocal]
      dsimp only [state]
      rw [show ({(frame original supply old.frame) with word := []}) =
        frame original supply {old.frame with word := []} from rfl,
        step_preserves_the_actual_frame]
      simp only [frame, List.length_map, List.map_drop, List.map_append, List.map_map]
      rfl

/-- Every finite future, for every old local policy and history-adaptive rival,
uses the existing interpreter and retains actual time, requests, packets and
their absolute timestamps. No future success certificate is an input. -/
theorem every_future_cut_is_preserved (policy : Option original.Policy)
    (oldInput : Input original) (old : State original) (count : Nat) :
    run (code original supply) policy (input original supply oldInput) (state original supply old) count =
      state original supply (run original policy oldInput old count) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih, advance_preserves_the_whole_actual_state]

variable [DecidableEq Port] [DecidableEq Technology]

def resume (source : Machine Party Good Port Technology Instrument)
    (supply : Supply source.code) (sourceInput : Input source.code) (cut : Nat) :
    Nat → State (code source.code supply)
  | 0 => state source.code supply (source.feedbackState sourceInput cut)
  | count + 1 => advance (code source.code supply) (source.feedbackPolicy (cut + count))
      (input source.code supply sourceInput) (resume source supply sourceInput cut count)

theorem resume_keeps_every_actual_source_step (source : Machine Party Good Port Technology Instrument)
    (supply : Supply source.code) (sourceInput : Input source.code) (cut count : Nat) :
    resume source supply sourceInput cut count =
      state source.code supply (source.feedbackState sourceInput (cut + count)) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [resume, ih, advance_preserves_the_whole_actual_state]
    rfl

theorem resume_uses_the_actual_saved_cut (source : Machine Party Good Port Technology Instrument)
    (supply : Supply source.code) (sourceInput : Input source.code) (cut : Nat) :
    (resume source supply sourceInput cut 0).current = (source.feedbackState sourceInput cut).current ∧
      (resume source supply sourceInput cut 0).history = (source.feedbackState sourceInput cut).history ∧
      (resume source supply sourceInput cut 0).frame.inbox = (source.feedbackState sourceInput cut).frame.inbox ∧
      (resume source supply sourceInput cut 0).frame.sent =
        (source.feedbackState sourceInput cut).frame.sent.map (packet source.code supply) := ⟨rfl,rfl,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension
