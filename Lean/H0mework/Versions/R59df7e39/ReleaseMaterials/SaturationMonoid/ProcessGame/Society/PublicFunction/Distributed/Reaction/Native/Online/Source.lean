import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Continuation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Material requests change history and cumulative word coordinates, without
    inventing a communication event or consuming the opponent's next decision. -/
def observeRaw (code : Code Party Good Port Technology Instrument)
    (state : Feedback.State code) (word : RawEvent Party Good Port Technology Instrument) : Feedback.State code :=
  {state with current := code.law.next state.current word
              history := state.history ++ [word]
              frame := {state.frame with word := state.frame.word ++ word}}

def observeActual (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth : Nat) : Nat → Feedback.State source.code
  | 0 => first
  | n+1 => observeRaw source.code (observeActual source first depth n)
      (source.actualExecution (depth+n)).submitted

theorem observed_actual_current (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth : Nat)
    (aligned : first.current = source.currentAt (depth+1)) (n : Nat) :
    (observeActual source first depth n).current = source.currentAt (depth+n+1) := by
  induction n with
  | zero => exact aligned
  | succ n ih =>
    change source.code.law.next (observeActual source first depth n).current
      (source.actualExecution (depth+n)).submitted = _
    rw [ih]
    exact (source.next_is_actual (depth+n)).symm

theorem observed_actual_budget (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth n : Nat) :
    (observeActual source first depth n).remaining = first.remaining := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem observed_actual_history (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth n : Nat) :
    (observeActual source first depth n).history = first.history ++
      (List.range n).map (fun index => (source.actualExecution (depth+index)).submitted) := by
  induction n with
  | zero => simp [observeActual]
  | succ n ih =>
    change (observeActual source first depth n).history ++ [(source.actualExecution (depth+n)).submitted] = _
    rw [ih]
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.append_assoc]

theorem observed_actual_frame (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth n : Nat) :
    (observeActual source first depth n).frame.word = first.frame.word ++
      ((List.range n).map (fun index => (source.actualExecution (depth+index)).submitted)).flatten := by
  induction n with
  | zero => simp [observeActual]
  | succ n ih =>
    change (observeActual source first depth n).frame.word ++ (source.actualExecution (depth+n)).submitted = _
    rw [ih]
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.flatten_append,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]

theorem observed_actual_communication (source : Machine Party Good Port Technology Instrument)
    (first : Feedback.State source.code) (depth n : Nat) :
    (observeActual source first depth n).past = first.past ∧
    (observeActual source first depth n).frame.inbox = first.frame.inbox ∧
    (observeActual source first depth n).frame.sent = first.frame.sent := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih => exact ih

private def stateCast {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (state : Feedback.State first) : Feedback.State second := same ▸ state
private def inputCast {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (input : Feedback.Input first) : Feedback.Input second := same ▸ input
omit [DecidableEq Port] [DecidableEq Technology] in
private theorem stateCast_current {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (state : Feedback.State first) : (stateCast same state).current = state.current := by
  cases same;rfl
omit [DecidableEq Port] [DecidableEq Technology] in
private theorem stateCast_budget {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (state : Feedback.State first) : (stateCast same state).remaining = state.remaining := by
  cases same;rfl
omit [DecidableEq Port] [DecidableEq Technology] in
private theorem inputCast_same {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (input : Feedback.Input first) : HEq (inputCast same input) input := by
  cases same;rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem stateCast_memory {first second : Code Party Good Port Technology Instrument}
    (same : first = second) (state : Feedback.State first) :
    (stateCast same state).frame.word = state.frame.word ∧
    HEq (stateCast same state).past state.past ∧
    HEq (stateCast same state).frame.inbox state.frame.inbox ∧
    HEq (stateCast same state).frame.sent state.frame.sent := by
  cases same
  exact ⟨rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

private theorem walk_ordered
    {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    {oldDepth : Nat} {word : List (Future.Recovery.Action old)}
    {start : Future.Recovery.Cursor old oldDepth word} (walk : Future.Recovery.Walk start) :
    start.depth ≤ walk.finish.depth := by
  induction walk with
  | finished => exact Nat.le_refl _
  | blocked cursor head _ _ _ => change cursor.depth ≤ cursor.depth+1;omega
  | unsupported cursor _ _ => change cursor.depth ≤ cursor.depth+1;omega
  | unpaid cursor fee _ _ => change cursor.depth ≤ cursor.depth+1+1;omega
  | billed cursor fee _ _ _ ih => exact (Nat.le_succ cursor.depth).trans ih
  | advanced cursor head _ _ _ _ ih => exact (Nat.le_succ cursor.depth).trans ih
  | workloadStopped cursor _ made _ =>
    have bound := made.preserves.depth
    change cursor.depth ≤ made.endpoint.depth+1;omega
  | workloadAdvanced cursor _ made _ _ ih => exact made.preserves.depth.trans ih
  | quotedStopped cursor _ made _ =>
    have bound := made.preserves.depth
    change cursor.depth ≤ made.endpoint.depth+1;omega
  | quotedAdvanced cursor _ made _ _ ih => exact made.preserves.depth.trans ih

def forecastWords (code : Code Party Good Port Technology Instrument)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) :
    Nat → List (RawEvent Party Good Port Technology Instrument)
  | 0 => []
  | n+1 => forecastWords code schedule input state n ++
      [Feedback.word code (schedule n) input (Feedback.Residual.run code schedule input state n)]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem forecast_length (code : Code Party Good Port Technology Instrument)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) (n : Nat) :
    (forecastWords code schedule input state n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forecastWords,List.length_append,List.length_singleton,ih]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem forecast_is_the_generated_history_suffix (code : Code Party Good Port Technology Instrument)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) (n : Nat) :
    (Feedback.Residual.run code schedule input state n).history = state.history ++ forecastWords code schedule input state n := by
  induction n with
  | zero => exact (List.append_nil _).symm
  | succ n ih =>
    rw [Feedback.Residual.run,Feedback.history_keeps_every_actual_word,ih,forecastWords,List.append_assoc]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem forecast_current (code : Code Party Good Port Technology Instrument)
    (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (state : Feedback.State code) (n : Nat) :
    (Feedback.Residual.run code schedule input state n).current =
      (forecastWords code schedule input state n).foldl code.law.next state.current := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change code.law.next (Feedback.Residual.run code schedule input state n).current _ = _
    rw [ih,forecastWords,List.foldl_append,List.foldl_cons,List.foldl_nil]

variable (seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (driver : Feedback.Input seed.source.code)

/-- All constructors are producers below. No caller supplies a frame, endpoint,
    future input table, or proof of a selected future. -/
structure Cursor where
  private mk ::
  source : Authority.Sources seed.base seed.scope
  count : Nat
  feedbackIndex : Nat
  input : Feedback.Input source.val.code
  state : Feedback.State source.val.code
  same_code : source.val.code = seed.source.code
  same_driver : HEq input driver
  aligned : state.current = source.val.currentAt (Machine.Continuation.depth source.val count+1)

def start (cut : Nat) (active : seed.source.feedback? = some driver) (empty : seed.source.continuation = []) :
    Cursor seed driver :=
  ⟨Authority.sourceIndex seed,cut,cut,driver,seed.source.feedbackState driver cut,rfl,HEq.rfl,by
    have actual := seed.source.feedback_current_is_actual driver active empty cut
    change (seed.source.feedbackState driver cut).current = seed.source.currentAt (seed.source.history.length+1+cut+1)
    rw [show seed.source.history.length+1+cut+1 = seed.source.history.length+2+cut by omega]
    exact actual.symm⟩

abbrev boundAt (origin : Authority.Sources seed.base seed.scope) : Authority.Bound
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨seed.base,seed.scope,origin.val,origin.property.1,origin.property.2⟩

namespace Cursor
variable {seed driver} (cursor : Cursor seed driver)

abbrev model : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨seed.base,seed.scope,cursor.source.val,cursor.source.property.1,cursor.source.property.2⟩
abbrev depth := Machine.Continuation.depth cursor.source.val cursor.count
abbrev policy := cursor.source.val.feedbackPolicy cursor.feedbackIndex
abbrev emitted := Feedback.word cursor.source.val.code cursor.policy cursor.input cursor.state

private theorem appended_alignment (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    cursor.source.val.code.law.next cursor.state.current word =
      (Machine.Continuation.extend cursor.source.val cursor.count word).currentAt
        (Machine.Continuation.depth (Machine.Continuation.extend cursor.source.val cursor.count word) (cursor.count+1)+1) := by
  rw [cursor.aligned]
  have next := Machine.Continuation.actual_next cursor.source.val cursor.count word
  simpa only [Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation,Nat.add_assoc] using next.symm

def submit (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) : Cursor seed driver :=
  ⟨⟨Machine.Continuation.extend cursor.source.val cursor.count word,cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+1,cursor.feedbackIndex,cursor.input,observeRaw cursor.source.val.code cursor.state word,
    cursor.same_code,cursor.same_driver,cursor.appended_alignment word⟩

def poll : Cursor seed driver :=
  ⟨⟨Machine.Continuation.extend cursor.source.val cursor.count cursor.emitted,cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+1,cursor.feedbackIndex+1,cursor.input,
    Feedback.advance cursor.source.val.code cursor.policy cursor.input cursor.state,
    cursor.same_code,cursor.same_driver,cursor.appended_alignment cursor.emitted⟩

theorem submit_is_the_actual_word (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    ((cursor.submit word).source.val.actualExecution cursor.depth).submitted = word :=
  Machine.Continuation.submitted cursor.source.val cursor.count word

theorem poll_is_the_actual_word :
    (cursor.poll.source.val.actualExecution cursor.depth).submitted = cursor.emitted :=
  Machine.Continuation.submitted cursor.source.val cursor.count cursor.emitted

theorem poll_uses_the_current_delivered_observation :
    Feedback.decision cursor.source.val.code cursor.input cursor.state =
      if cursor.state.remaining = 0 then none
      else cursor.input.opponent cursor.state.history cursor.state.past cursor.state.frame := rfl

theorem raw_work_preserves_input_budget_and_communication (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    (cursor.submit word).state.remaining = cursor.state.remaining ∧
    (cursor.submit word).feedbackIndex = cursor.feedbackIndex ∧
    (cursor.submit word).state.past = cursor.state.past ∧
    (cursor.submit word).state.frame.inbox = cursor.state.frame.inbox ∧
    (cursor.submit word).state.frame.sent = cursor.state.frame.sent := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem raw_work_is_recorded_in_the_complete_history (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    (cursor.submit word).state.history = cursor.state.history ++ [word] ∧
    (cursor.submit word).state.frame.word = cursor.state.frame.word ++ word := ⟨rfl,rfl⟩

theorem poll_advances_the_original_event_kernel :
    cursor.poll.state = Feedback.advance cursor.source.val.code cursor.policy cursor.input cursor.state := rfl

theorem every_polled_request_has_its_own_real_before :
    (cursor.poll.source.val.actualExecution cursor.depth).before = cursor.state.current := by
  exact (Machine.Continuation.before cursor.source.val cursor.count cursor.emitted).trans cursor.aligned.symm

theorem raw_work_keeps_every_prior_native_financial_origin (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input (cursor.submit word).source.val.input
      (Financial.accountAt cursor.source.val.input ordinal)
      (Financial.accountAt (cursor.submit word).source.val.input ordinal) :=
  Machine.Continuation.complete_financial_prefix cursor.source.val cursor.count word ordinal earlier

theorem polling_keeps_every_prior_native_financial_origin (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input cursor.poll.source.val.input
      (Financial.accountAt cursor.source.val.input ordinal)
      (Financial.accountAt cursor.poll.source.val.input ordinal) :=
  Machine.Continuation.complete_financial_prefix cursor.source.val cursor.count cursor.emitted ordinal earlier

def install (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)) :=
  cursor.source.val.withContinuation
    (Machine.Continuation.past cursor.source.val cursor.count ++ words ++ cursor.source.val.continuation.drop cursor.count)

private theorem install_earlier_body
    (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (ordinal : Nat) (earlier : ordinal < cursor.depth) :
    (cursor.install words).body (cursor.source.val.currentAt (ordinal+1)) =
      cursor.source.val.body (cursor.source.val.currentAt (ordinal+1)) := by
  have address : (cursor.source.val.currentAt (ordinal+1)).round-cursor.source.val.code.initial.round-1 = ordinal := by
    rw [cursor.source.val.current_round];omega
  rw [← cursor.source.val.actual_word ordinal]
  simp only [install,Machine.withContinuation,Machine.body,address]
  by_cases old : ordinal < cursor.source.val.history.length
  · rw [List.getElem?_eq_getElem old]
    exact (cursor.source.val.history_word_is_actual ordinal old).symm
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt old)]
    by_cases later : cursor.source.val.history.length < ordinal
    · have inside : ordinal-cursor.source.val.history.length-1 < cursor.count := by
        dsimp only [depth,Machine.Continuation.depth] at earlier;omega
      rw [if_pos later,List.getElem?_append_left (by rw [List.length_append,Machine.Continuation.past_length];omega),
        List.getElem?_append_left (by rw [Machine.Continuation.past_length];exact inside)]
      simp only [Machine.Continuation.past,List.getElem?_ofFn,dif_pos inside]
      have index : cursor.source.val.history.length+1+(ordinal-cursor.source.val.history.length-1) = ordinal := by omega
      rw [index]
    · rw [if_neg later]
      have same : ordinal = cursor.source.val.history.length := by omega
      subst ordinal
      rw [cursor.source.val.actual_word,Machine.body,address,List.getElem?_eq_none (le_refl _),if_neg (Nat.lt_irrefl _)]
      rfl

theorem install_prior_events (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
    ProgrammeSource.rawEvent (cursor.install words).input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current := by
  cases ordinal with
  | zero => rfl
  | succ ordinal =>
    obtain ⟨current,previous,view⟩ : ∃ current past, (ProgrammeHistory.visitAt cursor.source.val.input (ordinal+1)).current = .running current past := by
      cases visit : (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current <;>
        simp only [ProgrammeHistory.visitAt,ProgrammeSource.next,visit] <;> exact ⟨_,_,rfl⟩
    have body := cursor.install_earlier_body words ordinal (by omega)
    change ProgrammeSource.rawEvent (cursor.install words).input _ = _
    rw [view]
    change (cursor.install words).body current = cursor.source.val.body current
    simpa only [Machine.currentAt,view,ProgrammeSource.rawCurrent] using body

theorem install_prior_currents (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    (ProgrammeHistory.visitAt (cursor.install words).input ordinal).current =
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.actual_prefix_from_events cursor.source.val.input (cursor.install words).input rfl rfl
    (cursor.depth+1) (cursor.install_prior_events words) ordinal earlier

theorem install_word (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (index : Nat) (inside : index < words.length) :
    ((cursor.install words).actualExecution (cursor.depth+index)).submitted = words[index] := by
  have bound : cursor.count+index < (cursor.install words).continuation.length := by
    simp only [install,Machine.withContinuation,List.length_append,Machine.Continuation.past_length];omega
  have actual := (cursor.install words).continuation_word_is_actual (cursor.count+index) bound
  have address : (cursor.install words).history.length+1+(cursor.count+index) = cursor.depth+index := by
    dsimp only [install,Machine.withContinuation,depth,Machine.Continuation.depth];omega
  rw [address] at actual
  have directBound : cursor.count+index < ((Machine.Continuation.past cursor.source.val cursor.count ++ words) ++ cursor.source.val.continuation.drop cursor.count).length := by
    simpa only [install,Machine.withContinuation] using bound
  have lookup : ((Machine.Continuation.past cursor.source.val cursor.count ++ words) ++ cursor.source.val.continuation.drop cursor.count)[cursor.count+index]'directBound = words[index] := by
    rw [List.getElem_append_left (by rw [List.length_append,Machine.Continuation.past_length];omega),
      List.getElem_append_right (by rw [Machine.Continuation.past_length];omega)]
    simp only [Machine.Continuation.past_length,Nat.add_sub_cancel_left]
  exact actual.trans lookup

theorem install_current (words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (n : Nat) (bounded : n ≤ words.length) :
    (cursor.install words).currentAt (cursor.depth+n+1) =
      (words.take n).foldl cursor.source.val.code.law.next cursor.state.current := by
  induction n with
  | zero =>
    change (cursor.install words).currentAt (cursor.depth+1) = cursor.state.current
    unfold Machine.currentAt
    rw [cursor.install_prior_currents words _ (Nat.le_refl _)]
    exact cursor.aligned.symm
  | succ n ih =>
    have inside : n < words.length := by omega
    have emitted := cursor.install_word words n inside
    rw [show cursor.depth+(n+1)+1 = (cursor.depth+n)+2 by omega,
      (cursor.install words).next_is_actual,emitted]
    rw [show cursor.depth+n+1 = cursor.depth+n+1 from rfl,ih (by omega),List.take_succ_eq_append_getElem inside,
      List.foldl_append,List.foldl_cons,List.foldl_nil]
    rfl

/-- Append a finite raw prefix, retaining each native event and the original observation budget. -/
def submitPrefix (words : List (List (Future.Recovery.Action cursor.model))) : Cursor seed driver :=
  ⟨⟨{cursor.source.val with
        continuation := if words.isEmpty then cursor.source.val.continuation else (cursor.install words).continuation
        feedback? := if words.isEmpty then cursor.source.val.feedback? else none},
      cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+words.length,cursor.feedbackIndex,cursor.input,
    {cursor.state with current := words.foldl cursor.source.val.code.law.next cursor.state.current
                       history := if words.isEmpty then cursor.state.history else cursor.state.history ++ words
                       frame := {cursor.state.frame with word := if words.isEmpty then cursor.state.frame.word
                         else cursor.state.frame.word ++ words.flatten}},
    cursor.same_code,cursor.same_driver,by
      cases words with
      | nil => exact cursor.aligned
      | cons head tail =>
        have actual := cursor.install_current (head::tail) (head::tail).length (Nat.le_refl _)
        rw [List.take_length] at actual
        change _ = (cursor.install (head::tail)).currentAt
          (cursor.source.val.history.length+1+(cursor.count+(head::tail).length)+1)
        rw [show cursor.source.val.history.length+1+(cursor.count+(head::tail).length)+1 =
          cursor.depth+(head::tail).length+1 by dsimp only [depth,Machine.Continuation.depth];omega]
        exact actual.symm⟩

theorem submitPrefix_empty_is_the_original_cursor : cursor.submitPrefix [] = cursor := rfl

def forecast (schedule : Feedback.Residual.Schedule cursor.source.val.code)
    (rival : Opponent cursor.source.val.code) (n : Nat) :=
  cursor.install (forecastWords cursor.source.val.code schedule ⟨rival,cursor.input.budget⟩ cursor.state n)

def realize (schedule : Feedback.Residual.Schedule cursor.source.val.code) (n : Nat) : Cursor seed driver :=
  let words := forecastWords cursor.source.val.code schedule cursor.input cursor.state n
  ⟨⟨cursor.install words,cursor.source.property.1,cursor.source.property.2⟩,
    cursor.count+n,cursor.feedbackIndex+n,cursor.input,
    Feedback.Residual.run cursor.source.val.code schedule cursor.input cursor.state n,
    cursor.same_code,cursor.same_driver,by
      have current := cursor.install_current words n (by rw [forecast_length])
      rw [show words.take n = words by rw [← forecast_length cursor.source.val.code schedule cursor.input cursor.state n];exact List.take_length] at current
      change _ = (cursor.install words).currentAt (cursor.source.val.history.length+1+(cursor.count+n)+1)
      rw [show cursor.source.val.history.length+1+(cursor.count+n)+1 = cursor.depth+n+1 by dsimp only [depth,Machine.Continuation.depth];omega]
      exact (forecast_current cursor.source.val.code schedule cursor.input cursor.state n).trans current.symm⟩

theorem polling_advances_the_actual_depth : cursor.poll.depth = cursor.depth+1 := by
  change cursor.source.val.history.length+1+(cursor.count+1) = cursor.source.val.history.length+1+cursor.count+1
  omega

theorem realization_advances_the_actual_depth
    (schedule : Feedback.Residual.Schedule cursor.source.val.code) (n : Nat) :
    (cursor.realize schedule n).depth = cursor.depth+n := by
  change cursor.source.val.history.length+1+(cursor.count+n) = cursor.source.val.history.length+1+cursor.count+n
  omega

theorem realize_is_the_generated_actual_forecast
    (schedule : Feedback.Residual.Schedule cursor.source.val.code) (n : Nat) :
    (cursor.realize schedule n).source.val = cursor.forecast schedule cursor.input.opponent n := rfl

variable {origin : Authority.Sources seed.base seed.scope} {oldDepth : Nat} {word : List (Future.Recovery.Action seed)}
    {original : Future.Receipt (boundAt seed origin) oldDepth cursor.source cursor.count word}

private theorem origin_code (made : Future.Recovery.Output original) :
    made.bound.source.code = cursor.source.val.code := made.walk.source_code_is_retained

private theorem origin_begin_current (made : Future.Recovery.Output original) :
    made.bound.source.currentAt (cursor.depth+1) = cursor.source.val.currentAt (cursor.depth+1) := by
  have events (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
      ProgrammeSource.rawEvent made.bound.source.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
        ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current := by
    have later := made.walk.prior_events ordinal (by
      change ordinal < cursor.depth+1+1;omega)
    have previous : (ProgrammeHistory.visitAt (Future.Recovery.begin original).source.val.input ordinal).current =
        (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
      Machine.Continuation.prior_currents cursor.source.val cursor.count _ ordinal (Nat.le_of_lt earlier)
    rw [previous] at later
    exact later.trans (Machine.Continuation.prior_events cursor.source.val cursor.count _ ordinal earlier)
  have current := Machine.actual_prefix_from_events cursor.source.val.input made.bound.source.input
    (congrArg Code.law (cursor.origin_code made))
    (congrArg Code.initial (cursor.origin_code made)) (cursor.depth+1) events (cursor.depth+1) (Nat.le_refl _)
  unfold Machine.currentAt
  rw [current]
  cases (ProgrammeHistory.visitAt cursor.source.val.input (cursor.depth+1)).current with
  | bootstrap => exact congrArg Code.initial (cursor.origin_code made)
  | running => rfl

/-- Re-read every newly emitted word from this actual priced output. The frame
    is generated from the old frame and the exact paid interval, never supplied. -/
def assimilate (made : Future.Recovery.Output original) : Cursor seed driver :=
  let same := cursor.origin_code made
  let initial := stateCast same.symm cursor.state
  let state := observeActual made.bound.source initial cursor.depth (made.walk.finish.depth-cursor.depth)
  ⟨Authority.sourceIndex made.bound,made.walk.finish.count,cursor.feedbackIndex,
    inputCast same.symm cursor.input,state,same.trans cursor.same_code,
    (inputCast_same same.symm cursor.input).trans cursor.same_driver,by
      have aligned : initial.current = made.bound.source.currentAt (cursor.depth+1) :=
        (stateCast_current same.symm cursor.state).trans (cursor.aligned.trans (cursor.origin_begin_current made).symm)
      have current := observed_actual_current made.bound.source initial cursor.depth aligned (made.walk.finish.depth-cursor.depth)
      have ordered := walk_ordered made.walk
      have first : (Future.Recovery.begin original).depth = cursor.depth+1 := rfl
      rw [first] at ordered
      have address : cursor.depth+(made.walk.finish.depth-cursor.depth)+1 = made.walk.finish.depth+1 := by omega
      rw [address] at current
      exact current⟩

theorem assimilation_has_the_same_actual_source (made : Future.Recovery.Output original) :
    (cursor.assimilate made).model = made.bound := by
  cases made.walk.finish.model
  rfl

theorem assimilation_preserves_the_actual_depth_order (made : Future.Recovery.Output original) :
    cursor.depth ≤ (cursor.assimilate made).depth := by
  have ordered := walk_ordered made.walk
  have first : (Future.Recovery.begin original).depth = cursor.depth+1 := rfl
  rw [first] at ordered
  change cursor.depth ≤ made.walk.finish.depth
  omega

theorem assimilation_does_not_spend_a_feedback_decision (made : Future.Recovery.Output original) :
    (cursor.assimilate made).feedbackIndex = cursor.feedbackIndex := rfl

theorem all_assimilated_invoices_and_retries_preserve_the_next_input_budget (made : Future.Recovery.Output original) :
    (cursor.assimilate made).state.remaining = cursor.state.remaining :=
  (observed_actual_budget _ _ _ _).trans (stateCast_budget _ _)

theorem assimilated_frame_contains_every_actual_invoice_and_retry (made : Future.Recovery.Output original) :
    (cursor.assimilate made).state.frame.word = cursor.state.frame.word ++
      ((List.range (made.walk.finish.depth-cursor.depth)).map
        (fun index => (made.bound.source.actualExecution (cursor.depth+index)).submitted)).flatten :=
  (observed_actual_frame _ _ _ _).trans
    (congrArg (fun prior => prior ++ _) (stateCast_memory _ _).1)

theorem assimilation_preserves_communication_without_fabricating_events (made : Future.Recovery.Output original) :
    HEq (cursor.assimilate made).state.past cursor.state.past ∧
    HEq (cursor.assimilate made).state.frame.inbox cursor.state.frame.inbox ∧
    HEq (cursor.assimilate made).state.frame.sent cursor.state.frame.sent := by
  have memory := observed_actual_communication made.bound.source
    (stateCast (cursor.origin_code made).symm cursor.state) cursor.depth (made.walk.finish.depth-cursor.depth)
  have casted := stateCast_memory (cursor.origin_code made).symm cursor.state
  exact ⟨(heq_of_eq memory.1).trans casted.2.1,
    (heq_of_eq memory.2.1).trans casted.2.2.1,(heq_of_eq memory.2.2).trans casted.2.2.2⟩

variable {oldDepth : Nat} {word : List (Future.Recovery.Action seed)}
    {original : Future.Receipt seed oldDepth cursor.source cursor.count word}

def recover (made : Future.Recovery.Output original) : Cursor seed driver :=
  cursor.assimilate (origin := Authority.sourceIndex seed) made

theorem recovery_has_the_same_actual_source (made : Future.Recovery.Output original) :
    (cursor.recover made).model = made.bound := cursor.assimilation_has_the_same_actual_source (origin := Authority.sourceIndex seed) made

theorem recovery_does_not_spend_a_feedback_decision (made : Future.Recovery.Output original) :
    (cursor.recover made).feedbackIndex = cursor.feedbackIndex := rfl

theorem all_recovery_invoices_and_retries_preserve_the_next_input_budget (made : Future.Recovery.Output original) :
    (cursor.recover made).state.remaining = cursor.state.remaining :=
  cursor.all_assimilated_invoices_and_retries_preserve_the_next_input_budget (origin := Authority.sourceIndex seed) made

theorem recovery_frame_contains_every_actual_invoice_and_retry (made : Future.Recovery.Output original) :
    (cursor.recover made).state.frame.word = cursor.state.frame.word ++
      ((List.range (made.walk.finish.depth-cursor.depth)).map
        (fun index => (made.bound.source.actualExecution (cursor.depth+index)).submitted)).flatten :=
  cursor.assimilated_frame_contains_every_actual_invoice_and_retry (origin := Authority.sourceIndex seed) made

theorem recovery_preserves_communication_without_fabricating_events (made : Future.Recovery.Output original) :
    HEq (cursor.recover made).state.past cursor.state.past ∧
    HEq (cursor.recover made).state.frame.inbox cursor.state.frame.inbox ∧
    HEq (cursor.recover made).state.frame.sent cursor.state.frame.sent :=
  cursor.assimilation_preserves_communication_without_fabricating_events (origin := Authority.sourceIndex seed) made

end Cursor
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online
