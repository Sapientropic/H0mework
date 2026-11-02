import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Continuation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Feedback
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- A World refusal remains its own typed result while the original drive continues. -/
inductive WorldResult (state : Inquiry.Frame task) where
  | short (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (missing : ¬ Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + World.units task input))
  | completed (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (covered : Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + World.units task input))
      (selected : World.Selection task input state)

namespace WorldResult
variable {task} {state : Inquiry.Frame task}
def candidate? : WorldResult task state → Option (Prefix.Global.Candidate (tariff := task.recoveryPricing)
    (requested := task.futureRequests) task.model task.domain task.original state.past state.programme)
  | .short .. => none
  | .completed _ _ _ _ _ selected => World.Selection.candidate? task selected

def service {cache : Inquiry.Frame task} (step : Stage task cache) (generated : step = stage task cache)
    (permit : Permit task step.path.finish) (paid : step.ready = some permit) :
    WorldResult task step.path.finish → Service task cache
  | .short input supplied rate declared missing =>
      .worldShort step generated permit paid input supplied rate declared missing
  | .completed input supplied rate declared covered selected =>
      .worldCompleted step generated permit paid input supplied rate declared covered selected
end WorldResult

inductive Walk : Inquiry.Frame task → Type where
  | paused {cache} : Walk cache
  | unavailable {cache} (step : Stage task cache) (generated : step = stage task cache)
      (missing : step.ready = none) : Walk cache
  | continued {cache} (step : Stage task cache) (generated : step = stage task cache)
      (missing : step.ready = none) (live : Driving.Progress.Live step.path.finish.shell)
      (later : Walk (Inquiry.Frame.advance task step.path.finish)) : Walk cache
  | selected {cache} (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (candidate : Prefix.Global.Candidate (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme)
      (compiled : Prefix.Global.compile (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme = .selected candidate) : Walk cache
  | repaired {cache} (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (rejected : ∀ tail,Prefix.Global.Failure (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.programme
        (Prefix.Global.proposal task.model task.domain step.path.finish.past tail))
      (compiled : Prefix.Global.compile (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original step.path.finish.past step.path.finish.programme = .blocked rejected)
      (reply : Repair.Response step.path.finish
        (rejected (Repair.remaining task step.path.finish step.path.finish.programme)))
      (generatedReply : reply = Repair.respond step.path.finish
        (rejected (Repair.remaining task step.path.finish step.path.finish.programme)))
      (later : Walk reply.path.finish) : Walk cache


  | world {cache} (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (result : WorldResult task step.path.finish)
      (later : Unit → Walk (Inquiry.Frame.advance task step.path.finish)) : Walk cache

/-- Each next service starts from the preceding actual work endpoint. -/
def run : Nat → (cache : Inquiry.Frame task) → Walk task cache
  | 0,_ => .paused
  | count+1,cache => match GlobalPolicy.invoke task cache with
      | .unavailable step generated missing =>
          if live : Driving.Progress.Live step.path.finish.shell then
            .continued step generated missing live (run count (Inquiry.Frame.advance task step.path.finish))
          else .unavailable step generated missing
      | .completed step generated permit paid outcome compiled => match outcome with
          | .selected candidate => .selected step generated permit paid candidate compiled.symm
          | .blocked rejected =>
              let reply := Repair.respond step.path.finish
                (rejected (Repair.remaining task step.path.finish step.path.finish.programme))
              .repaired step generated permit paid rejected compiled.symm reply rfl (run count reply.path.finish)


      | .worldShort step generated permit paid input supplied rate declared missing =>
          .world step generated permit paid (.short input supplied rate declared missing)
            (fun _ => run count (Inquiry.Frame.advance task step.path.finish))
      | .worldCompleted step generated permit paid input supplied rate declared covered selected =>
          .world step generated permit paid (.completed input supplied rate declared covered selected)
            (fun _ => run count (Inquiry.Frame.advance task step.path.finish))

private theorem leg_current {cache : Inquiry.Frame task} (path : Inquiry.Leg task cache) :
    (Planning.current task path.finish).point = Splice.install (Planning.current task cache).point task.rival path.word := by
  rw [Paid.State.current_is_the_actual_control_prefix path.finish.shell task.point task.rival,
    Paid.State.current_is_the_actual_control_prefix cache.shell task.point task.rival]
  change Splice.install task.point.point task.rival path.finish.past = _
  rw [path.literal]
  exact List.foldl_append

namespace Walk
variable {task} {cache : Inquiry.Frame task}

def word : {cache : Inquiry.Frame task} → Walk task cache → List (Prefix.Rule task.model.source.code)
  | _,.paused => []
  | _,.unavailable step _ _ => step.path.word
  | _,.continued step _ _ _ later => step.path.word ++ Driving.Progress.rules step.path.finish.shell ++ later.word
  | _,.selected step _ _ _ candidate _ => step.path.word ++
      Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol
  | _,.repaired step _ _ _ _ _ reply _ later => step.path.word ++ reply.path.word ++ later.word

  | _,.world step _ _ _ result later => match result.candidate? with
      | some candidate => step.path.word ++
          Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol
      | none => step.path.word ++ Driving.Progress.rules step.path.finish.shell ++ (later ()).word

def full : {cache : Inquiry.Frame task} → Walk task cache → Cursor task.model.source.code
  | cache,.paused => (Planning.current task cache).point
  | _,.unavailable step _ _ => (Planning.current task step.path.finish).point
  | _,.continued _ _ _ _ later => later.full
  | _,.selected step _ _ _ candidate _ => Splice.install (Planning.current task step.path.finish).point task.rival
      (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)
  | _,.repaired _ _ _ _ _ _ _ _ later => later.full

  | _,.world step _ _ _ result later => match result.candidate? with
      | some candidate => Splice.install (Planning.current task step.path.finish).point task.rival
          (Prefix.Runtime.suffix (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol)
      | none => (later ()).full

def programme : {cache : Inquiry.Frame task} → Walk task cache → Program task.model.source.code (horizon task.domain)
  | cache,.paused => cache.programme
  | _,.unavailable step _ _ => step.path.finish.programme
  | _,.continued _ _ _ _ later => later.programme
  | _,.selected _ _ _ _ candidate _ => candidate.protocol
  | _,.repaired _ _ _ _ _ _ _ _ later => later.programme

  | _,.world _ _ _ _ result later => match result.candidate? with
      | some candidate => candidate.protocol
      | none => (later ()).programme

theorem actual_source (made : Walk task cache) :
    made.full = Splice.install (Planning.current task cache).point task.rival made.word := by
  induction made with
  | paused => rfl
  | unavailable step => exact leg_current task step.path
  | continued step _ _ _ later ih =>
      simp only [full,word]
      have advanced : (Planning.current task (Inquiry.Frame.advance task step.path.finish)).point =
          Splice.install (Planning.current task step.path.finish).point task.rival
            (Driving.Progress.rules step.path.finish.shell) := by
        simpa only [Inquiry.Leg.advance] using leg_current task (Inquiry.Leg.advance step.path.finish)
      rw [ih,advanced,leg_current task step.path]
      simp only [Splice.install,List.foldl_append]
  | selected step _ _ _ candidate _ =>
      change Splice.install (Planning.current task step.path.finish).point task.rival _ = _
      rw [leg_current task step.path]
      exact (List.foldl_append ..).symm
  | repaired step _ _ _ _ _ reply _ later ih =>
      change later.full = Splice.install (Planning.current task _).point task.rival _
      rw [ih]
      change Splice.install reply.full task.rival later.word = _
      rw [reply.actual_source,leg_current task step.path]
      simp only [word,Splice.install,List.foldl_append]

  | world step _ _ _ result later ih =>
      cases found : result.candidate? with
      | some candidate =>
          simp only [full,word]
          rw [found]
          rw [leg_current task step.path]
          exact (List.foldl_append ..).symm
      | none =>
          simp only [full,word]
          rw [found]
          have advanced : (Planning.current task (Inquiry.Frame.advance task step.path.finish)).point =
              Splice.install (Planning.current task step.path.finish).point task.rival
                (Driving.Progress.rules step.path.finish.shell) := by
            simpa only [Inquiry.Leg.advance] using leg_current task (Inquiry.Leg.advance step.path.finish)
          rw [ih (),advanced,leg_current task step.path]
          simp only [Splice.install,List.foldl_append]

theorem restores (made : Walk task cache) :
    Inquiry.Preservation.Restoration.Accepts task cache.programme made.programme := by
  induction made with
  | @paused cache => exact Inquiry.Preservation.Restoration.self task cache.shell
  | unavailable step generated _ =>
      simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task _
  | continued step generated _ _ later ih =>
      exact Inquiry.Preservation.Restoration.trans task
        (by simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task _)
        (Inquiry.Preservation.Restoration.trans task (Inquiry.Preservation.Restoration.frame_advance task _) ih)
  | selected step generated _ _ candidate _ =>
      exact Inquiry.Preservation.Restoration.trans task
        (by simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task _) candidate.fullAccepted
  | repaired step generated _ _ _ _ reply _ _ ih =>
      exact Inquiry.Preservation.Restoration.trans task
        (by simpa only [programme,generated] using Inquiry.Preservation.Restoration.stage task _)
        (Inquiry.Preservation.Restoration.trans task reply.restores ih)

  | @world cache step generated _ _ result later ih =>
      have charged : Inquiry.Preservation.Restoration.Accepts task cache.programme step.path.finish.programme := by
        simpa only [generated] using Inquiry.Preservation.Restoration.stage task cache
      cases found : result.candidate? with
      | some candidate =>
          simp only [programme]
          rw [found]
          exact Inquiry.Preservation.Restoration.trans task charged candidate.fullAccepted
      | none =>
          simp only [programme]
          rw [found]
          exact Inquiry.Preservation.Restoration.trans task charged
            (Inquiry.Preservation.Restoration.trans task (Inquiry.Preservation.Restoration.frame_advance task _) (ih ()))

theorem settles (made : Walk task cache) :
    Inquiry.Preservation.Accepts task cache.programme made.programme :=
  Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ made.restores

def Audit : {cache : Inquiry.Frame task} → Walk task cache → Prop
  | _,.paused => True
  | _,.unavailable step _ _ => step.ready = none
  | _,.continued step generated missing _ later =>
      (Service.unavailable step generated missing).Contract ∧
      Inquiry.Preservation.Restoration.Accepts task step.path.finish.programme
        (Inquiry.Frame.advance task step.path.finish).programme ∧ later.Audit
  | _,.selected step generated permit paid candidate compiled =>
      (Service.completed step generated permit paid (.selected candidate) compiled.symm).Contract
  | _,.repaired step generated permit paid rejected compiled reply _ later =>
      (Service.completed step generated permit paid (.blocked rejected) compiled.symm).Contract ∧
      Inquiry.Preservation.Restoration.Accepts task step.path.finish.programme reply.path.finish.programme ∧
      reply.path.finish.past.length = step.path.finish.past.length+1 ∧ later.Audit

  | _,.world step generated permit paid result later =>
      (result.service step generated permit paid).Contract ∧
      ∀ _ : result.candidate? = none, (later ()).Audit

theorem audited (made : Walk task cache) : made.Audit := by
  induction made with
  | paused => trivial
  | unavailable _ _ missing => exact missing
  | continued step generated missing _ later ih =>
      exact ⟨Service.contract (.unavailable step generated missing),Inquiry.Preservation.Restoration.frame_advance task _,ih⟩
  | selected step generated permit paid candidate compiled => exact Service.contract (.completed step generated permit paid (.selected candidate) compiled.symm)
  | repaired step generated permit paid rejected compiled reply _ later ih =>
      exact ⟨Service.contract (.completed step generated permit paid (.blocked rejected) compiled.symm),
        reply.restores,reply.advances permit.live,ih⟩

  | world step generated permit paid result _ ih =>
      exact ⟨Service.contract (result.service step generated permit paid),fun _ => ih ()⟩

def LocalDomain (frame : Inquiry.Frame task) : Prop :=
  Knowledge.Contains frame.views (Planning.current task frame) ∧
  Distributed.Recall.Information.Agency.Protocol.Continuation.Covered
    (Planning.domain task frame) (Planning.current task frame).point

theorem local_domain (frame : Inquiry.Frame task)
    (covered : Knowledge.Contains frame.views (Planning.current task frame)) : LocalDomain frame := by
  refine ⟨covered,?_⟩
  exact Knowledge.cursor_covered _ _
    (Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain
      frame.views (Planning.current task frame) covered task.reader)

/-- Each continued cache retains the actual local knowledge used by the next fee gate. -/
def Knows : {cache : Inquiry.Frame task} → Walk task cache → Prop
  | cache,.paused => LocalDomain cache
  | _,.unavailable step _ _ => LocalDomain step.path.finish
  | _,.continued step _ _ _ later => LocalDomain step.path.finish ∧
      LocalDomain (Inquiry.Frame.advance task step.path.finish) ∧ later.Knows
  | _,.selected step _ _ _ _ _ => LocalDomain step.path.finish
  | _,.repaired step _ _ _ _ _ reply _ later =>
      LocalDomain step.path.finish ∧
      LocalDomain reply.path.finish ∧ later.Knows

  | _,.world step _ _ _ result later => LocalDomain step.path.finish ∧
      ∀ _ : result.candidate? = none,
        LocalDomain (Inquiry.Frame.advance task step.path.finish) ∧ (later ()).Knows

theorem knowledge (made : Walk task cache)
    (covered : Knowledge.Contains cache.views (Planning.current task cache)) : made.Knows := by
  induction made with
  | paused => exact local_domain _ covered
  | unavailable step => exact local_domain _ (step.path.knowledge covered)
  | selected step => exact local_domain _ (step.path.knowledge covered)
  | continued step _ _ _ later ih =>
      have paid := step.path.knowledge covered
      have next := Inquiry.Frame.advance_knowledge task _ paid
      exact ⟨local_domain _ paid,local_domain _ next,ih next⟩
  | repaired step _ _ _ _ _ reply _ later ih =>
      have paid := step.path.knowledge covered
      have next := reply.path.knowledge paid
      exact ⟨local_domain _ paid,local_domain _ next,ih next⟩

  | world step _ _ _ result later ih =>
      have paid := step.path.knowledge covered
      have next := Inquiry.Frame.advance_knowledge task _ paid
      exact ⟨local_domain _ paid,fun _ => ⟨local_domain _ next,ih () next⟩⟩

def paidStarts : {cache : Inquiry.Frame task} → Walk task cache → List (View (code := task.model.source.code))
  | _,.paused => []
  | _,.unavailable _ _ _ => []
  | _,.continued _ _ _ _ later => later.paidStarts
  | cache,.selected _ _ _ _ _ _ => [Planning.current task cache]
  | cache,.repaired _ _ _ _ _ _ _ _ later => Planning.current task cache :: later.paidStarts

  | cache,.world _ _ _ _ result later => Planning.current task cache ::
      match result.candidate? with
      | some _ => []
      | none => (later ()).paidStarts

theorem each_new_service_has_its_own_actual_payment (made : Walk task cache)
    (point : View (code := task.model.source.code)) (inside : point ∈ made.paidStarts) :
    Charge.paid task.quote task.model task.reader point task.rival
      (Charge.endAt task.quote task.model task.reader point task.rival) := by
  induction made with
  | paused | unavailable => cases inside
  | continued _ _ _ _ later ih => exact ih inside
  | @selected cache step _ permit paid _ _ =>
      have same : point = Planning.current task cache := by simpa only [paidStarts,List.mem_singleton] using inside
      subst point
      exact step.charged (by rw [paid];rfl)
  | repaired step _ permit paid _ _ _ _ later ih =>
      rcases List.mem_cons.mp inside with same | rest
      · subst point;exact step.charged (by rw [paid];rfl)
      · exact ih rest

  | @world cache step _ permit paid result later ih =>
      simp only [paidStarts] at inside
      rcases List.mem_cons.mp inside with same | rest
      · subst point
        exact step.charged (by rw [paid];rfl)
      · cases found : result.candidate? with
        | some candidate =>
            rw [found] at rest
            exact False.elim (List.not_mem_nil rest)
        | none =>
            rw [found] at rest
            exact ih () rest

theorem complete_initial_financial_prefix (made : Walk task cache) (visit : Nat)
    (earlier : visit ≤ arrival (Planning.current task cache).point) :
    Native.Coupling.Match task.model.source.code (Planning.current task cache).point.source.input made.full.source.input
      (Financial.accountAt (Planning.current task cache).point.source.input visit) (Financial.accountAt made.full.source.input visit) := by
  rw [made.actual_source]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := task.model) _ task.rival _ visit earlier

abbrev bound (made : Walk task cache) := Replanning.native task.model made.full
abbrev facade (made : Walk task cache) := Native.AuthorityRuntime.facade made.bound
abbrev activated (made : Walk task cache) := Inquiry.Runtime.readState made.bound (depth made.full)

theorem the_same_actual_root_consumes_the_entire_paid_feedback_chain_and_its_own_next (made : Walk task cache) :
    let active := made.activated
    made.Audit ∧ Inquiry.Preservation.Restoration.Accepts task cache.programme made.programme ∧
    HEq (made.facade.readoutAt active .responsibilities) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .responsibilities
  exact ⟨made.audited,made.restores,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Walk

/-- Exhaustion of an observer counter is separate from economic closure. -/
def Walk.Closed : {cache : Inquiry.Frame task} → Walk task cache → Prop
  | cache,.paused => cache.past.length = (Computation.Cut.seed task.point.point).remaining
  | _,.unavailable step _ _ => ¬ Driving.Progress.Live step.path.finish.shell
  | _,.continued _ _ _ _ later => later.Closed
  | _,.selected _ _ _ _ _ _ => True
  | _,.repaired _ _ _ _ _ _ _ _ later => later.Closed

  | _,.world _ _ _ _ result later => ∀ _ : result.candidate? = none, (later ()).Closed

theorem enough_actual_stages_close_the_generated_chain (count : Nat) (cache : Inquiry.Frame task)
    (enough : (Computation.Cut.seed task.point.point).remaining ≤ cache.past.length+count) :
    (run task count cache).Closed := by
  induction count generalizing cache with
  | zero =>
      have bounded : cache.past.length ≤ (Computation.Cut.seed task.point.point).remaining := cache.actualWithin
      change cache.past.length = _
      omega
  | succ count ih =>
      cases produced : GlobalPolicy.invoke task cache with
      | unavailable step generated missing =>
          simp only [run,produced]
          split
          · rename_i live
            apply ih
            have extension : cache.past.length ≤ step.path.finish.past.length := by
              rw [step.path.literal]
              simp only [List.length_append]
              omega
            have advanced : (Inquiry.Frame.advance task step.path.finish).past.length = step.path.finish.past.length+1 := by
              rw [Inquiry.Frame.advance_past]
              simp only [Driving.Progress.rules,if_pos live,List.length_append,List.length_singleton]
            rw [advanced]
            omega
          · assumption
      | completed step generated permit paid outcome compiled =>
          cases outcome with
          | selected => simp only [run,produced,Walk.Closed]
          | blocked rejected =>
              let reply := Repair.respond step.path.finish
                (rejected (Repair.remaining task step.path.finish step.path.finish.programme))
              have next : (Computation.Cut.seed task.point.point).remaining ≤ reply.path.finish.past.length+count := by
                have extension : cache.past.length ≤ step.path.finish.past.length := by
                  rw [step.path.literal]
                  simp only [List.length_append]
                  omega
                have advanced := reply.advances permit.live
                omega
              simpa only [run,produced,Walk.Closed] using ih reply.path.finish next


      | worldShort step generated permit paid input supplied rate declared missing =>
          simp only [run,produced,Walk.Closed]
          intro _
          apply ih
          have extension : cache.past.length ≤ step.path.finish.past.length := by
            rw [step.path.literal]
            simp only [List.length_append]
            omega
          have advanced : (Inquiry.Frame.advance task step.path.finish).past.length = step.path.finish.past.length+1 := by
            rw [Inquiry.Frame.advance_past]
            simp only [Driving.Progress.rules,if_pos permit.live,List.length_append,List.length_singleton]
          rw [advanced]
          omega
      | worldCompleted step generated permit paid input supplied rate declared covered selected =>
          simp only [run,produced,Walk.Closed]
          intro _
          apply ih
          have extension : cache.past.length ≤ step.path.finish.past.length := by
            rw [step.path.literal]
            simp only [List.length_append]
            omega
          have advanced : (Inquiry.Frame.advance task step.path.finish).past.length = step.path.finish.past.length+1 := by
            rw [Inquiry.Frame.advance_past]
            simp only [Driving.Progress.rules,if_pos permit.live,List.length_append,List.length_singleton]
          rw [advanced]
          omega

/-- The continuation allowance is computed from the actual unspent history. -/
def execute (cache : Inquiry.Frame task) : Walk task cache :=
  run task ((Computation.Cut.seed task.point.point).remaining-cache.past.length) cache

theorem the_source_budget_never_mistakes_a_live_pause_for_closure (cache : Inquiry.Frame task) :
    (execute task cache).Closed := by
  apply enough_actual_stages_close_the_generated_chain
  have bounded : cache.past.length ≤ (Computation.Cut.seed task.point.point).remaining := cache.actualWithin
  omega

inductive Output where
  | rejected (row : Selection.Rejection task.model task.domain task.original task.baseline task.baseline)
  | generated (cache : Inquiry.Frame task) (walk : Walk task cache)

def produce : Output task := match Owned.Source.seed task with
  | .rejected row => .rejected row
  | .accepted cache _ _ _ => .generated (Inquiry.Frame.pack cache) (execute task (Inquiry.Frame.pack cache))

namespace Public
variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor (RecallBirth.code request)) (future : Opponent (RecallBirth.code request)) (localRounds : Nat)

abbrev Prior := Local.Output (RecallBirth.born request) quotas point future localRounds

def Follow : Prior request quotas point future localRounds → Type
  | .inherited _ => Unit
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      Walk task (Inquiry.Frame.pack actual.1)

def follow (prior : Prior request quotas point future localRounds) : Follow request quotas point future localRounds prior :=
  match prior with
  | .inherited _ => ()
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      execute task (Inquiry.Frame.pack actual.1)

def produce :=
  let prior := Local.produce (RecallBirth.born request) quotas point future localRounds
  Sigma.mk prior (follow request quotas point future localRounds prior)

def Contract (prior : Prior request quotas point future localRounds)
    (next : Follow request quotas point future localRounds prior) : Prop :=
  prior.Sound ∧ match prior,next with
  | .inherited _,_ => True
  | .installed fits _ _ choice _ actual _,next =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      next.Closed ∧ next.Audit ∧ next.Knows ∧
      Selection.acceptable task.model task.domain task.original (PaidSearch.reference (RecallBirth.born request) _ fits) next.programme ∧
      next.full = Splice.install (Planning.current task (Inquiry.Frame.pack actual.1)).point task.rival next.word

theorem follows_the_original_source_and_responsibility (prior : Prior request quotas point future localRounds)
    (sound : prior.Sound) : Contract request quotas point future localRounds prior
      (follow request quotas point future localRounds prior) := by
  refine ⟨sound,?_⟩
  cases prior with
  | inherited => trivial
  | installed fits work released choice selected actual generated =>
      let task := PublicTask.Feedback.task (RecallBirth.born request) _ fits quotas point future choice
      let made := execute task (Inquiry.Frame.pack actual.1)
      refine ⟨the_source_budget_never_mistakes_a_live_pause_for_closure task _,made.audited,made.knowledge sound.2.1,?_,made.actual_source⟩
      have carried := Inquiry.Preservation.trans task actual.1.above made.settles
      exact Selection.acceptable_trans _ _ _ _ _ _ carried choice.policy.accepted

theorem every_legal_public_history_generates_its_actual_paid_feedback_chain
    (origin : Distributed.Recall.Information.Origin (RecallBirth.native request))
    (stages : List (EventHistory.Stage (code := RecallBirth.code request)))
    (installed : stages.map Prod.fst = (RecallBirth.born request).installed) :
    let point := EventHistory.execute (EventHistory.ofOrigin (RecallBirth.native request) request.budget origin) stages
    let made := produce request quotas point future localRounds
    Contract request quotas point future localRounds made.1 made.2 :=
  follows_the_original_source_and_responsibility request quotas _ future localRounds _
    (Local.all_public_histories_generate_actual_local_installation
      (RecallBirth.born request) quotas future localRounds origin stages installed)
end Public

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Feedback
