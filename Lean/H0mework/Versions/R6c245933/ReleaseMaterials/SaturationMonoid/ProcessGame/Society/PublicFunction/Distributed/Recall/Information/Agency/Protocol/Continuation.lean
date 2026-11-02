import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

/-- The source fields retain a fixed public Code across every installed control. -/
structure Cursor where
  reference : code.Policy
  reference_generated : reference ∈ code.policies
  history : History (Party := Party) (Good := Good) (Port := Port)
    (Technology := Mandate.State Party Technology) (Instrument := Instrument)
  original : history ∈ code.histories
  opponent : Opponent code
  side : Side
  entry : Input code
  overrides : List (Nat × Option code.Policy)
  cut : Nat
  ownerStart : Nat

namespace Cursor
variable {code}

abbrev source (cursor : Cursor code) : Machine Party Good Port (Mandate.State Party Technology) Instrument where
  code := code
  reference := cursor.reference
  reference_generated := cursor.reference_generated
  history := cursor.history
  original := cursor.original
  opponent := cursor.opponent
  side := cursor.side
  feedback? := some cursor.entry
  feedbackOverrides := cursor.overrides

variable (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)

abbrev controller := driver code cursor.ownerStart protocol rival
abbrev target := Future.target cursor.source cursor.entry cursor.cut (controller cursor protocol rival)
  (term cursor.source cursor.entry cursor.cut protocol).val
abbrev targetInput := Future.takeover cursor.source cursor.entry cursor.cut (controller cursor protocol rival)

def after : Cursor code :=
  let next := target cursor protocol rival
  ⟨next.reference,next.reference_generated,next.history,next.original,next.opponent,next.side,
    targetInput cursor protocol rival,next.feedbackOverrides,cursor.cut+1,cursor.ownerStart⟩

theorem after_is_the_protocols_own_actual_source :
    (after cursor protocol rival).source = target cursor protocol rival := rfl

theorem after_has_its_own_input_and_next_cut :
    (after cursor protocol rival).entry = targetInput cursor protocol rival ∧
    (after cursor protocol rival).cut = cursor.cut+1 := ⟨rfl,rfl⟩

end Cursor

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

def ofWorld (world : World model budget) : Cursor model.source.code :=
  let source := world.source model budget
  ⟨source.reference,source.reference_generated,source.history,source.original,source.opponent,source.side,
    world.input model budget,source.feedbackOverrides,world.phase.val,Agency.start source world.phase.val⟩

theorem original_world_is_its_own_cursor (world : World model budget) :
    (ofWorld model budget world).source = world.source model budget ∧
    (ofWorld model budget world).entry = world.input model budget ∧
    (ofWorld model budget world).cut = world.phase.val := ⟨rfl,rfl,rfl⟩

def initial : List (Cursor model.source.code) := (worlds model budget).map (ofWorld model budget)

def advance (domain : List (Cursor code)) (protocol : Rule code) : List (Cursor code) :=
  domain.flatMap fun cursor =>
    (Cut.tables cursor.source cursor.entry cursor.cut).map fun table =>
      cursor.after protocol (Cut.opponent cursor.source cursor.entry cursor.cut table)

def history (installed : List (Rule model.source.code)) : List (Cursor model.source.code) :=
  installed.foldl (advance model.source.code) (initial model budget)

theorem every_original_world_is_in_the_initial_domain (world : World model budget) :
    ofWorld model budget world ∈ initial model budget :=
  List.mem_map.mpr ⟨world,every_world_is_generated model budget world,rfl⟩

theorem every_generated_table_produces_its_own_successor
    (domain : List (Cursor code)) (protocol : Rule code) (cursor : Cursor code)
    (inside : cursor ∈ domain) (table : Cut.Table cursor.source cursor.entry cursor.cut)
    (generated : table ∈ Cut.tables cursor.source cursor.entry cursor.cut) :
    cursor.after protocol (Cut.opponent cursor.source cursor.entry cursor.cut table) ∈ advance code domain protocol :=
  List.mem_flatMap.mpr ⟨cursor,inside,List.mem_map.mpr ⟨table,generated,rfl⟩⟩

variable {code} (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)

abbrev externalTable : Cut.Table cursor.source cursor.entry cursor.cut :=
  Residual.restrict code (Residual.seed cursor.source cursor.entry cursor.cut)
    (Residual.schedules cursor.source cursor.entry cursor.cut) rival

abbrev finiteRival : Opponent code := Cut.opponent cursor.source cursor.entry cursor.cut (externalTable cursor rival)

theorem one_original_external_table_preserves_every_actual_ordinal_state (n : Nat) :
    (Cursor.target cursor protocol (finiteRival cursor rival)).feedbackState
        (Cursor.targetInput cursor protocol (finiteRival cursor rival)) (cursor.cut+n) =
    (Cursor.target cursor protocol rival).feedbackState
        (Cursor.targetInput cursor protocol rival) (cursor.cut+n) := by
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state]
  let schedule := Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val
  have generated : schedule ∈ Residual.schedules cursor.source cursor.entry cursor.cut :=
    List.mem_map.mpr ⟨_,(term cursor.source cursor.entry cursor.cut protocol).property,rfl⟩
  change Residual.run code schedule ⟨Cursor.controller cursor protocol (finiteRival cursor rival),cursor.entry.budget⟩
      (Residual.seed cursor.source cursor.entry cursor.cut) n =
    Residual.run code schedule ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩
      (Residual.seed cursor.source cursor.entry cursor.cut) n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [ih]
    let actual := Residual.run code schedule ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩
      (Residual.seed cursor.source cursor.entry cursor.cut) n
    change Reaction.Feedback.advance code (schedule n)
        ⟨Cursor.controller cursor protocol (finiteRival cursor rival),cursor.entry.budget⟩ actual =
      Reaction.Feedback.advance code (schedule n) ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩ actual
    by_cases exhausted : actual.remaining = 0
    · simp only [Reaction.Feedback.advance,word,decision,exhausted,if_pos]
    · have bounded : n < (Residual.seed cursor.source cursor.entry cursor.cut).remaining := by
        have remaining := Residual.remaining_is_the_seed_budget code schedule
          ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩
          (Residual.seed cursor.source cursor.entry cursor.cut) n
        change actual.remaining = _ at remaining
        omega
      have keyed := Residual.every_remaining_decision_is_generated code
        (Residual.seed cursor.source cursor.entry cursor.cut) (Residual.schedules cursor.source cursor.entry cursor.cut)
        schedule generated ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩ n bounded
      rw [Residual.advance_is_its_actual_choice,Residual.advance_is_its_actual_choice]
      apply congrArg (fun move => Residual.forced code (schedule n) move actual)
      change driver code cursor.ownerStart protocol (finiteRival cursor rival)
          actual.history actual.past actual.frame =
        driver code cursor.ownerStart protocol rival actual.history actual.past actual.frame
      simp only [driver]
      cases ownerAt code cursor.ownerStart actual.history.length with
      | some site => rfl
      | none =>
        simp only [finiteRival,Cut.opponent,Residual.respond]
        have present : (actual.history,actual.past,actual.frame) ∈
            Residual.keys code (Residual.seed cursor.source cursor.entry cursor.cut)
              (Residual.schedules cursor.source cursor.entry cursor.cut) := keyed
        simp only [dif_pos present,externalTable,Residual.restrict]


private abbrev replay (opponent : Opponent code) (n : Nat) :=
  Residual.run code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val)
    ⟨Cursor.controller cursor protocol opponent,cursor.entry.budget⟩
    (Residual.seed cursor.source cursor.entry cursor.cut) n

private theorem same_replay (n : Nat) :
    replay cursor protocol (finiteRival cursor rival) n = replay cursor protocol rival n := by
  have same := one_original_external_table_preserves_every_actual_ordinal_state cursor protocol rival n
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
  exact same

private theorem replay_words (n : Nat) :
    word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n)
        ⟨Cursor.controller cursor protocol (finiteRival cursor rival),cursor.entry.budget⟩
        (replay cursor protocol (finiteRival cursor rival) n) =
    word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n)
        ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩ (replay cursor protocol rival n) := by
  have words := congrArg State.history (same_replay cursor protocol rival (n+1))
  simp only [replay,Residual.run,history_keeps_every_actual_word] at words
  have same := same_replay cursor protocol rival n
  dsimp only [replay] at same
  rw [same] at words
  simpa only [replay,same] using List.singleton_inj.mp (List.append_cancel_left words)

private theorem feedback_history_length
    (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
    (entry : Input source.code) (n : Nat) :
    (source.feedbackState entry n).history.length = source.history.length+1+n := by
  induction n with
  | zero => simp [Machine.feedbackState,Machine.feedbackInitial]
  | succ n ih =>
    change (Reaction.Feedback.advance source.code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

private theorem replay_history_length (opponent : Opponent code) (n : Nat) :
    (replay cursor protocol opponent n).history.length = cursor.source.history.length+1+cursor.cut+n := by
  induction n with
  | zero => exact feedback_history_length cursor.source cursor.entry cursor.cut
  | succ n ih =>
    change (Reaction.Feedback.advance code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

private theorem body_from_replay (opponent : Opponent code)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat)
    (rounds : current.round = code.initial.round+(cursor.source.history.length+2+(cursor.cut+n))) :
    (Cursor.target cursor protocol opponent).body current =
      word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n)
        ⟨Cursor.controller cursor protocol opponent,cursor.entry.budget⟩ (replay cursor protocol opponent n) := by
  unfold Machine.body
  rw [rounds]
  have address : code.initial.round+(cursor.source.history.length+2+(cursor.cut+n))-code.initial.round-1 =
      cursor.source.history.length+1+(cursor.cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Cursor.target,Future.target,Execution.target];omega),
    if_pos (by dsimp only [Cursor.target,Future.target,Execution.target];omega)]
  simp only []
  rw [show cursor.source.history.length+1+(cursor.cut+n)-(Cursor.target cursor protocol opponent).history.length-1 =
    cursor.cut+n by change cursor.source.history.length+1+(cursor.cut+n)-cursor.source.history.length-1 = _;omega]
  change word code ((Cursor.target cursor protocol opponent).feedbackPolicy (cursor.cut+n))
    (Cursor.targetInput cursor protocol opponent)
    ((Cursor.target cursor protocol opponent).feedbackState (Cursor.targetInput cursor protocol opponent) (cursor.cut+n)) = _
  have policy := Execution.policy_at
    {cursor.source with feedback? := some (Cursor.targetInput cursor protocol opponent)} cursor.cut
    (term cursor.source cursor.entry cursor.cut protocol).val n
  change (Cursor.target cursor protocol opponent).feedbackPolicy (cursor.cut+n) =
    Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n at policy
  rw [policy,Future.the_whole_future_run_is_the_actual_state]
  simp only [word,decision,if_neg (show ¬(replay cursor protocol opponent n).history.length <
      cursor.source.history.length+1+cursor.cut by rw [replay_history_length];omega)]

/-- Exact raw events, not only balances, agree at every finite programme ordinal. -/
theorem one_external_table_preserves_every_raw_occurrence (ordinal : Nat) :
    ProgrammeSource.rawEvent (Cursor.target cursor protocol (finiteRival cursor rival)).input
        (ProgrammeHistory.visitAt (Cursor.target cursor protocol rival).input ordinal).current =
      ProgrammeSource.rawEvent (Cursor.target cursor protocol rival).input
        (ProgrammeHistory.visitAt (Cursor.target cursor protocol rival).input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt (Cursor.target cursor protocol rival).input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (Cursor.target cursor protocol (finiteRival cursor rival)).body current =
      (Cursor.target cursor protocol rival).body current
    have rounds := ProgrammeHistory.visit_round (Cursor.target cursor protocol rival).input ordinal
    rw [view] at rounds
    change current.round = code.initial.round+ordinal at rounds
    have source_length : cursor.source.history.length = cursor.history.length := rfl
    by_cases earlier : ordinal < cursor.source.history.length+2+cursor.cut
    · exact (Future.earlier_body cursor.source cursor.entry cursor.cut
        (Cursor.controller cursor protocol (finiteRival cursor rival))
        (term cursor.source cursor.entry cursor.cut protocol).val rfl current
          (by change current.round-code.initial.round-1 < cursor.source.history.length+1+cursor.cut;omega)).trans
        (Future.earlier_body cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival)
          (term cursor.source cursor.entry cursor.cut protocol).val rfl current
          (by change current.round-code.initial.round-1 < cursor.source.history.length+1+cursor.cut;omega)).symm
    · let n := ordinal-(cursor.source.history.length+2+cursor.cut)
      have indexed : ordinal = cursor.source.history.length+2+(cursor.cut+n) := by dsimp only [n];omega
      rw [body_from_replay cursor protocol (finiteRival cursor rival) current n (by omega),
        body_from_replay cursor protocol rival current n (by omega)]
      exact replay_words cursor protocol rival n


theorem one_external_table_preserves_the_complete_native_financial_history (ordinal : Nat) :
    Native.Coupling.Match code (Cursor.target cursor protocol rival).input
      (Cursor.target cursor protocol (finiteRival cursor rival)).input
      (Financial.accountAt (Cursor.target cursor protocol rival).input ordinal)
      (Financial.accountAt (Cursor.target cursor protocol (finiteRival cursor rival)).input ordinal) :=
  Native.Coupling.History.complete_accounts code (Cursor.target cursor protocol rival).input
    (Cursor.target cursor protocol (finiteRival cursor rival)).input rfl rfl ordinal
    (fun index _ => one_external_table_preserves_every_raw_occurrence cursor protocol rival index)
    (Cursor.target cursor protocol rival).body (Cursor.target cursor protocol (finiteRival cursor rival)).body
    rfl rfl ordinal (Nat.le_refl _)

def Covers (next : Cursor code) : Prop :=
  next.cut = cursor.cut+1 ∧ next.ownerStart = cursor.ownerStart ∧
    (∀ n, next.source.feedbackState next.entry (cursor.cut+n) =
      (Cursor.target cursor protocol rival).feedbackState (Cursor.targetInput cursor protocol rival) (cursor.cut+n)) ∧
    ∀ ordinal, Native.Coupling.Match code (Cursor.target cursor protocol rival).input next.source.input
      (Financial.accountAt (Cursor.target cursor protocol rival).input ordinal)
      (Financial.accountAt next.source.input ordinal)

theorem every_actual_successor_has_a_publicly_generated_representative
    (domain : List (Cursor code)) (inside : cursor ∈ domain) :
    ∃ next ∈ advance code domain protocol, Covers cursor protocol rival next := by
  refine ⟨cursor.after protocol (finiteRival cursor rival),
    every_generated_table_produces_its_own_successor code domain protocol cursor inside
      (externalTable cursor rival) (Residual.restriction_is_generated _ _ _ rival),
    rfl,rfl,?_,?_⟩
  · exact one_original_external_table_preserves_every_actual_ordinal_state cursor protocol rival
  · exact one_external_table_preserves_the_complete_native_financial_history cursor protocol rival

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat)
  (world : World model budget) (installed : Rule model.source.code) (environment : Opponent model.source.code)

structure Transition where
  domain : List (Cursor model.source.code)
  public_history : domain = history model budget [installed]
  actual_covered : ∃ next ∈ domain, Covers (ofWorld model budget world) installed environment next

def generate : Transition model budget world installed environment where
  domain := advance model.source.code (initial model budget) installed
  public_history := rfl
  actual_covered := every_actual_successor_has_a_publicly_generated_representative
    (ofWorld model budget world) installed environment (initial model budget)
    (every_original_world_is_in_the_initial_domain model budget world)

theorem the_generated_domain_uses_no_hidden_actual_world
    (other : World model budget) (rival : Opponent model.source.code) :
    (generate model budget world installed environment).domain = (generate model budget other installed rival).domain := rfl

theorem the_first_installed_cursor_is_the_actual_protocol_target :
    Cursor.target (ofWorld model budget world) installed environment =
      target (world.source model budget) (world.input model budget) world.phase.val installed environment := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation
