import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Source
open EnergyRenewal.Privacy (SourceInput ResultRel)

/-- This predicate only reads the complete public item emitted by the original execution. -/
def Opens (scope : Scope) (item : PublicItem) : Prop :=
  item.request=liftAudit item.before applicationFee ∧ item.accepted=true ∧
    Quiet (audit item.before) ∧ scope.task.deadline < item.before.clock

def OpeningCondition (scope : Scope) (item : ExecutionItem Actor Good Port Technology Instrument) : Prop :=
  item.request=liftAudit item.before applicationFee ∧ (law scope).Valid item.before item.request ∧
    Quiet (audit item.before) ∧ scope.task.deadline < item.before.clock

theorem actual_opening_characterization (scope : Scope) (before : Current) (actions : List JointAction) :
    (opening scope before actions).isSome=true ↔ scope.task.deadline<before.clock ∧
      ∃ item∈cachedItems scope before actions,OpeningCondition scope item := by
  classical
  unfold Supply.opening
  by_cases expired : scope.task.deadline<before.clock
  · rw [if_pos expired,List.findSome?_isSome_iff]
    constructor
    · rintro ⟨item,_,flag⟩
      by_cases good : OpeningCondition scope item.val
      · exact ⟨expired,item.val,item.property,good⟩
      · simp only [OpeningCondition] at good
        rw [dif_neg good] at flag
        contradiction
    · rintro ⟨_,item,member,good⟩
      refine ⟨⟨item,member⟩,by simp,?_⟩
      simp only [OpeningCondition] at good
      rw [dif_pos good]
      rfl
  · simp [expired]

theorem opening_is_public (scope : Scope) (before : Current) (actions : List JointAction) :
    (opening scope before actions).isSome=true ↔ scope.task.deadline<before.clock ∧
      ∃ item∈publicItems scope before actions 0,Opens scope item := by
  rw [actual_opening_characterization]
  simp [publicItems,Opens,OpeningCondition,cachedItems_exact,RawLaw.rawItems,
    publicize,rebuild,liftAudit,liftAuditOperation,audit,Quiet]

theorem Twin.opening {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) :
    (Supply.opening scope left actions).isSome=(Supply.opening scope right actions).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [opening_is_public,opening_is_public,same.clock,same.publicItems scope cost actions safe 0]

theorem Source.SessionTwin.prepared {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right) :
    Supply.Privacy.Twin left.prepared right.prepared := by
  unfold Session.prepared
  rw [←same.scope]
  exact same.current.next left.window.scope rfl [] (by simp)

theorem Source.SessionTwin.actions {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right)
    (query : Query) (mode : Mode) : left.actions query mode=right.actions query mode := by
  unfold Session.actions
  rw [←same.scope,←same.target]
  exact same.prepared.word left.window.scope rfl left.target query mode

theorem Source.SessionTwin.after {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right)
    (query : Query) (mode : Mode) : Supply.Privacy.Twin (left.after query mode) (right.after query mode) := by
  unfold Session.after
  rw [cachedNext_exact,cachedNext_exact,←same.scope,←same.actions query mode]
  exact same.prepared.next left.window.scope rfl _ (word_safe _ _ _ _ _)

theorem Source.SessionTwin.opening {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right)
    (query : Query) (mode : Mode) : (left.opening query mode).isSome=(right.opening query mode).isSome := by
  unfold Session.opening
  rw [←same.scope,←same.actions query mode]
  exact same.prepared.opening left.window.scope rfl _ (word_safe _ _ _ _ _)

theorem Source.SessionTwin.nextWindow {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right)
    (query : Query) (mode : Mode) :
    (left.nextWindow query mode).isSome=(right.nextWindow query mode).isSome ∧
    ((left.nextWindow query mode).getD left.window).scope=((right.nextWindow query mode).getD right.window).scope := by
  have opening := same.opening query mode
  have after := same.after query mode
  cases l : left.opening query mode with
  | none =>
    cases r : right.opening query mode with
    | none => simp [Session.nextWindow,l,r,same.scope]
    | some receipt => simp [l,r] at opening
  | some receipt =>
    cases r : right.opening query mode with
    | none => simp [l,r] at opening
    | some other =>
      simp only [Session.nextWindow,l,r]
      rw [←after.claims]
      split
      · refine ⟨rfl,?_⟩
        simp only [Option.getD_some,Continuation.Window.scope,audit,after.clock]
      · exact ⟨rfl,same.scope⟩

theorem Source.SessionTwin.next {lp rp : Plan} {left : Session lp} {right : Session rp} (same : SessionTwin left right)
    (query : Query) (mode : Mode) : SessionTwin (left.next query mode) (right.next query mode) := by
  have nextWindow := same.nextWindow query mode
  refine ⟨?_,?_,?_,?_⟩
  · rw [left.next_is_the_same_actual_generated_next,right.next_is_the_same_actual_generated_next,
      left.after_is_own_root_next,right.after_is_own_root_next]
    exact same.after query mode
  · change ((Supply.Runtime.consume left query mode 1).window.getD left.window).scope=
      ((Supply.Runtime.consume right query mode 1).window.getD right.window).scope
    rw [(Supply.Runtime.consume left query mode 1).actualWindow,(Supply.Runtime.consume right query mode 1).actualWindow]
    exact nextWindow.2
  · change (if (Supply.Runtime.consume left query mode 1).window.isSome then
      replacement left.window.scope left.prepared else left.target)=
      (if (Supply.Runtime.consume right query mode 1).window.isSome then
      replacement right.window.scope right.prepared else right.target)
    rw [(Supply.Runtime.consume left query mode 1).actualWindow,(Supply.Runtime.consume right query mode 1).actualWindow]
    simp only [ite_true]
    rw [nextWindow.1,←same.scope,same.prepared.replacement left.window.scope,same.target]
  · change (left.history++[Record.mk (left.input query mode) 1]).length=
      (right.history++[Record.mk (right.input query mode) 1]).length
    simp only [List.length_append,List.length_singleton,same.history]

/-- Material and authority take their own actual next; Family accounts continue separately on their original admissions. -/
theorem source_runs_keep_related_sessions {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : SessionTwin left.session right.session) (requests : Nat → Query×Mode) (count : Nat) :
    SessionTwin (Finance.run left requests count).session (Finance.run right requests count).session := by
  induction count with
  | zero => exact same
  | succ n ih => exact ih.next (requests n).1 (requests n).2

structure Reply where
  scope : Scope
  nextScope : Scope
  actor : Party
  target : Party
  historyLength : Nat
  opening : Bool
  observation : Observation

def reply {plan : Plan} (state : Finance.State plan) (query : Query) (mode : Mode) : Reply :=
  ⟨state.session.window.scope,(state.session.next query mode).window.scope,state.session.actor,state.session.target,
   (state.session.next query mode).history.length,(state.session.nextWindow query mode).isSome,
   observe state.session.window.scope state.session.target query mode state.session.prepared⟩

theorem Source.SessionTwin.reply {lp rp : Plan} {left : Finance.State lp} {right : Finance.State rp}
    (same : SessionTwin left.session right.session) (query : Query) (mode : Mode) :
    reply left query mode=reply right query mode := by
  have next := same.next query mode
  have window := same.nextWindow query mode
  have observation := same.prepared.observe left.session.window.scope rfl left.session.target query mode
  simp only [Supply.Privacy.reply]
  rw [same.scope,next.scope,next.history,same.target,window.1]
  have actor : left.session.actor=right.session.actor := by
    simp only [Session.actor,same.prepared.technology,same.target]
  rw [actor]
  congr 1
  simpa only [same.scope,same.target] using observation

/-- Failed decoding is a public error and does not execute a new source step. -/
structure Command where
  request : Except String (Query×Mode)
  metadata : Lean.Json

def advance {plan : Plan} (state : Finance.State plan) (command : Command) : Finance.State plan :=
  match command.request with
  | .error _ => state
  | .ok (query,mode) => state.next query mode

def answer {plan : Plan} (state : Finance.State plan) (command : Command) : Except String Reply :=
  command.request.map fun (query,mode) => reply state query mode

abbrev Render := Command → Except String Reply → Lean.Json
abbrev Strategy := List Lean.Json → Nat → Command

def play {plan : Plan} (initial : Finance.State plan) (render : Render) (strategy : Strategy) :
    Nat → Finance.State plan × List Lean.Json
  | 0 => (initial,[])
  | n+1 =>
    let (state,past) := play initial render strategy n
    let command := strategy past n
    (advance state command,past++[render command (answer state command)])

theorem cumulative_related_own_states_and_complete_output {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp) (same : SessionTwin left.session right.session)
    (render : Render) (strategy : Strategy) (count : Nat) :
    SessionTwin (play left render strategy count).1.session (play right render strategy count).1.session ∧
      (play left render strategy count).2=(play right render strategy count).2 := by
  induction count with
  | zero => exact ⟨same,rfl⟩
  | succ n ih =>
    simp only [play,←ih.2]
    cases requested : (strategy (play left render strategy n).2 n).request with
    | error message =>
      simp only [advance,answer,requested,Except.map_error]
      exact ⟨ih.1,rfl⟩
    | ok request =>
      rcases request with ⟨query,mode⟩
      simp only [advance,answer,requested,Except.map_ok]
      exact ⟨ih.1.next query mode,by dsimp only [Except.map];rw [ih.1.reply query mode]⟩

def sourceOutput (larger : Bool) (input : SourceInput) (render : Render) (strategy : Strategy) (count : Nat) :
    Except String (List Lean.Json) :=
  (Source.initial larger input).map fun state => (play state render strategy count).2

/-- All complete public readouts, errors, metadata and adaptive commands are covered; initial worlds are source generated. -/
theorem every_source_strategy_keeps_complete_cumulative_supply_privacy (input : SourceInput)
    (render : Render) (strategy : Strategy) (count : Nat) :
    sourceOutput false input render strategy count=sourceOutput true input render strategy count := by
  have consume : ∀ {lp rp : Plan} {left : Except String (Finance.State lp)} {right : Except String (Finance.State rp)},
      ResultRel (fun l r => SessionTwin l.session r.session ∧ l.account=r.account) left right →
      left.map (fun state => (play state render strategy count).2)=
      right.map (fun state => (play state render strategy count).2) := by
    intro lp rp left right related
    cases related with
    | error _ => rfl
    | ok matched => exact congrArg Except.ok (cumulative_related_own_states_and_complete_output _ _ matched.1 render strategy count).2
  exact consume (Source.original_source_generates_new_supply_initial_relation input)

/-- The adaptive consumer keeps using the saved native account, including after public parse errors. -/
def play_financial_path {plan : Plan} (initial : Finance.State plan) (render : Render) (strategy : Strategy) (count : Nat) :
    (Financial.Family.process Finance.sources).Run initial.account.current (play initial render strategy count).1.account.current := by
  induction count with
  | zero => exact .nil
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial render strategy n).2 n).request with
    | error message => simpa only [advance,requested] using ih
    | ok request =>
      rcases request with ⟨query,mode⟩
      simp only [advance,requested]
      exact ih.concatRuns _ ((play initial render strategy n).1.transition query mode)

theorem every_adaptive_prefix_keeps_original_financial_admissions {plan : Plan}
    (initial : Finance.State plan) (render : Render) (strategy : Strategy) (count : Nat) :
    initial.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (play initial render strategy count).1.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial render strategy n).2 n).request with
    | error message => simpa only [advance,requested] using ih
    | ok request =>
      rcases request with ⟨query,mode⟩
      simp only [advance,requested]
      exact ih.trans ((play initial render strategy n).1.every_original_issued_claim_keeps_its_identity query mode)

theorem Session.own_private_frame_survives {plan : Plan} (session : Session plan) (query : Query) (mode : Mode) :
    ownFrame (session.next query mode).current=ownFrame session.current := by
  rw [session.next_is_the_same_actual_generated_next,session.after_is_own_root_next]
  unfold Session.after
  rw [cachedNext_exact]
  change ownFrame ((law session.window.scope).execute session.prepared 0 (session.actions query mode)).final=_
  rw [private_execute_is_its_own_frame session.window.scope rfl session.prepared (session.actions query mode)
    (word_safe session.window.scope session.target query mode session.prepared) 0]
  rfl

theorem every_adaptive_prefix_keeps_its_own_private_frame {plan : Plan}
    (initial : Finance.State plan) (render : Render) (strategy : Strategy) (count : Nat) :
    ownFrame (play initial render strategy count).1.session.current=ownFrame initial.session.current := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial render strategy n).2 n).request with
    | error message => simpa only [advance,requested] using ih
    | ok request =>
      rcases request with ⟨query,mode⟩
      simp only [advance,requested]
      exact (Session.own_private_frame_survives (play initial render strategy n).1.session query mode).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
