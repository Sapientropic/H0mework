import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Command where
  | work (requested : List (Future.Recovery.Action seed))
  | bill (units : Nat)
  | poll

variable (actor : Party) (position : Nat) (units : List Nat) (horizon : Nat)
def commands : List (Command seed) :=
  (words (Future.Recovery.Search.menu seed actor) seed.source.code.actionLimit).map Command.work ++
    units.map Command.bill ++ [Command.poll]

def programs := sequences (commands seed actor units) horizon
abbrev Program := {program // program ∈ programs seed actor units horizon}

variable {seed actor position units horizon}
  {actual : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input actual.source.code}
  (cursor : Cursor actual driver)

def Result : Command seed → Type
  | .work requested => Mandate.Replay.Path (base := actual.base) actual.scope cursor.state.current requested
  | .bill amount => Option {bill : Prefix.Bill cursor actor position // bill.before = [] ∧ bill.units = amount}
  | .poll => Unit

def evaluate : (command : Command seed) → Result (actor := actor) (position := position) cursor command
  | .work requested => Mandate.Replay.compile actual.base actual.scope cursor.state.current requested
  | .bill amount => Prefix.quote cursor actor position [] amount
  | .poll => ()

structure Receipt (command : Command seed) where
  private mk ::
  result : Result (actor := actor) (position := position) cursor command
  generated : result = evaluate cursor command

def perform (command : Command seed) : Receipt (actor := actor) (position := position) cursor command :=
  ⟨evaluate cursor command,rfl⟩

namespace Receipt
variable {cursor} {command : Command seed} (receipt : Receipt (actor := actor) (position := position) cursor command)
def endpoint : Cursor actual driver :=
  match command with
  | .work _ => cursor.submit receipt.result.output
  | .bill _ => match receipt.result with
    | none => cursor
    | some invoice => cursor.submit invoice.val.payment.output
  | .poll => cursor.poll

def emitted : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :=
  match command with
  | .work _ => [receipt.result.output]
  | .bill _ => match receipt.result with
    | none => []
    | some invoice => [invoice.val.payment.output]
  | .poll => [cursor.emitted]

theorem history_is_the_actual_emission :
    receipt.endpoint.state.history = cursor.state.history ++ receipt.emitted := by
  cases command with
  | work requested => rfl
  | bill amount =>
    rcases receipt with ⟨result,generated⟩
    cases result <;> simp [endpoint,emitted,Cursor.submit,observeRaw]
  | poll => exact Feedback.history_keeps_every_actual_word _ _ _ _

theorem count_is_the_actual_emission_count :
    receipt.endpoint.count = cursor.count + receipt.emitted.length := by
  cases command with
  | work requested => rfl
  | bill amount =>
    rcases receipt with ⟨result,generated⟩
    cases result <;> simp [endpoint,emitted,Cursor.submit]
  | poll => rfl

theorem keeps_the_original_unexecuted_native_tail :
    receipt.endpoint.source.val.continuation.drop receipt.endpoint.count =
      cursor.source.val.continuation.drop cursor.count := by
  cases command with
  | work requested => exact Machine.Continuation.pending_tail _ _ _
  | bill amount =>
    rcases receipt with ⟨result,generated⟩
    cases result with
    | none => rfl
    | some invoice => exact Machine.Continuation.pending_tail _ _ _
  | poll => exact Machine.Continuation.pending_tail _ _ _

theorem each_emission_is_its_original_native_source_word
    (index : Nat) (inside : index < receipt.emitted.length) :
    (receipt.endpoint.source.val.actualExecution (cursor.depth+index)).submitted = receipt.emitted[index] := by
  cases command with
  | work requested =>
    have zero : index = 0 := by simpa [emitted] using inside
    subst index
    exact cursor.submit_is_the_actual_word _
  | bill amount =>
    rcases receipt with ⟨result,generated⟩
    cases result with
    | none => simp [emitted] at inside
    | some invoice =>
      have zero : index = 0 := by simpa [emitted] using inside
      subst index
      simpa [endpoint,emitted] using cursor.submit_is_the_actual_word invoice.val.payment.output
  | poll =>
    have zero : index = 0 := by simpa [emitted] using inside
    subst index
    exact cursor.poll_is_the_actual_word
end Receipt

inductive Trace : Cursor actual driver → Type
  | done (cursor : Cursor actual driver) : Trace cursor
  | step {cursor : Cursor actual driver} (command : Command seed) (receipt : Receipt (actor := actor) (position := position) cursor command)
      (tail : Trace receipt.endpoint) : Trace cursor

def replay (cursor : Cursor actual driver) : List (Command seed) → Trace (seed := seed) (actor := actor) (position := position) cursor
  | [] => .done cursor
  | command :: tail =>
    let receipt := perform cursor command
    .step command receipt (replay receipt.endpoint tail)

namespace Trace
variable {cursor} (trace : Trace (seed := seed) (actor := actor) (position := position) cursor)
def endpoint : {cursor : Cursor actual driver} → Trace (seed := seed) (actor := actor) (position := position) cursor → Cursor actual driver
  | _, .done start => start
  | _, .step _ _ tail => endpoint tail

def emitted : {cursor : Cursor actual driver} → Trace (seed := seed) (actor := actor) (position := position) cursor →
    List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  | _, .done _ => []
  | _, .step _ receipt tail => receipt.emitted ++ emitted tail

theorem complete_actual_history :
    trace.endpoint.state.history = cursor.state.history ++ trace.emitted := by
  induction trace with
  | done start => simp [endpoint,emitted]
  | step command receipt tail ih =>
    change tail.endpoint.state.history = _
    rw [ih,receipt.history_is_the_actual_emission]
    simp only [emitted,List.append_assoc]

theorem actual_emission_count : trace.endpoint.count = cursor.count + trace.emitted.length := by
  induction trace with
  | done start => simp [endpoint,emitted]
  | step command receipt tail ih =>
    change tail.endpoint.count = _
    rw [ih,receipt.count_is_the_actual_emission_count]
    simp only [emitted,List.length_append,Nat.add_assoc]
theorem keeps_the_original_unexecuted_native_tail :
    trace.endpoint.source.val.continuation.drop trace.endpoint.count =
      cursor.source.val.continuation.drop cursor.count := by
  induction trace with
  | done start => rfl
  | step command receipt tail ih => exact ih.trans receipt.keeps_the_original_unexecuted_native_tail

end Trace

variable (seed actor position units horizon) (budget : Nat)
abbrev World := Distributed.Recall.Information.World seed budget

def canonicalWorld : World seed budget := by
  let origin : Distributed.Recall.Information.Origin seed :=
    ⟨⟨seed.source.history,seed.source.original⟩,
      ⟨Reaction.restrict seed.source.code (fun _ _ _ => none),
        Reaction.restriction_is_generated seed.source.code (fun _ _ _ => none)⟩,.original⟩
  let programme : Distributed.Recall.Information.Program seed budget :=
    ⟨List.replicate budget none,List.mem_filter.mpr ⟨
      (mem_sequences_iff _ _ _).mpr ⟨by simp,by
        intro control inside
        have same := List.eq_of_mem_replicate inside
        subst control
        exact List.mem_cons_self⟩,by simp⟩⟩
  let source := Distributed.Recall.Information.originSource seed budget origin
  let input := Distributed.Recall.Information.initialInput seed budget
  exact ⟨origin,programme,
    ⟨Feedback.Residual.restrict source.code (Feedback.Residual.seed source input 0)
        (Feedback.Residual.schedules source input 0) (fun _ _ _ => none),
      Feedback.Residual.restriction_is_generated source.code (Feedback.Residual.seed source input 0)
        (Feedback.Residual.schedules source input 0) (fun _ _ _ => none)⟩,
    ⟨0,Nat.zero_lt_succ budget⟩⟩

def initial (world : World seed budget) : Cursor (world.native seed budget) (world.input seed budget) :=
  start (world.native seed budget) (world.input seed budget) world.phase.val rfl rfl

structure Point where
  world : World seed budget
  program : Program seed actor units horizon

namespace Point
variable {seed actor position units horizon budget}
  (point : Point seed actor units horizon budget)
abbrev trace := replay (actor := actor) (position := position) (initial seed budget point.world) point.program.val
abbrev native := (point.trace (position := position)).endpoint

def signal (site : Fin seed.source.code.sites) : Fin seed.source.code.signals :=
  Observation.signal (seed := point.world.native seed budget) (point.native (position := position)) site

theorem keeps_the_whole_generated_raw_history :
    (point.native (position := position)).state.history =
      (initial seed budget point.world).state.history ++ (point.trace (position := position)).emitted :=
  (point.trace (position := position)).complete_actual_history
end Point

def points : List (Point seed actor units horizon budget) :=
  (Distributed.Recall.Information.worlds seed budget).flatMap fun world =>
    (programs seed actor units horizon).attach.map fun program => ⟨world,program⟩

theorem every_generated_actual_point_is_in_the_public_domain
    (point : Point seed actor units horizon budget) : point ∈ points seed actor units horizon budget := by
  refine List.mem_flatMap.mpr ⟨point.world,Distributed.Recall.Information.every_world_is_generated seed budget point.world,?_⟩
  exact List.mem_map.mpr ⟨point.program,List.mem_attach _ _,rfl⟩

def canonicalPoint : Point seed actor units horizon budget :=
  ⟨canonicalWorld seed budget,⟨[],(mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩⟩⟩

theorem the_public_domain_is_generated_nonempty : points seed actor units horizon budget ≠ [] :=
  List.ne_nil_of_mem (every_generated_actual_point_is_in_the_public_domain seed actor units horizon budget
    (canonicalPoint seed actor units horizon budget))

def fiber (site : Fin seed.source.code.sites) (reading : Fin seed.source.code.signals) :=
  (points seed actor units horizon budget).filter fun point => point.signal (position := position) site = reading

theorem in_fiber_exactly_for_the_actual_local_signal
    (site : Fin seed.source.code.sites) (reading : Fin seed.source.code.signals)
    (point : Point seed actor units horizon budget) :
    point ∈ fiber seed actor position units horizon budget site reading ↔
      point.signal (position := position) site = reading := by
  simp only [fiber,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun same => ⟨every_generated_actual_point_is_in_the_public_domain _ _ _ _ _ _,same⟩⟩

variable {seed actor position units horizon budget}
  {publicBudget publicFuel : Nat}
  {published : List (PublicRule seed.source.code)}
  {original fallback : PublicRule seed.source.code}
  {reference : PublicProgram seed.source.code publicFuel}
  (prepared : Prepared seed publicBudget published original reference fallback)
  (point : Point seed actor units horizon budget)

def requested (site : Fin seed.source.code.sites) :
    List (Future.Recovery.Action (point.native (position := position)).model) :=
  prepared.controller.work.val (site,point.signal (position := position) site) (seed.source.code.key_mem _)

theorem indistinguishable_native_points_receive_the_same_request
    (other : Point seed actor units horizon budget) (site : Fin seed.source.code.sites)
    (same : point.signal (position := position) site = other.signal (position := position) site) :
    requested (position := position) prepared point site = requested (position := position) prepared other site := by
  exact congrArg (fun signal => prepared.controller.work.val (site,signal) (seed.source.code.key_mem _)) same

theorem every_native_point_receives_an_original_registered_work_word
    (site : Fin seed.source.code.sites) :
    requested (position := position) prepared point site ∈ words (point.native (position := position)).source.val.code.actions
      (point.native (position := position)).source.val.code.actionLimit := by
  rw [(point.native (position := position)).same_code]
  exact (List.mem_pi _ _).mp prepared.controller.work.property _ (seed.source.code.key_mem _)

variable {pricing : Future.Recovery.Pricing (Future.Recovery.Action (point.native (position := position)).model)}
  {n : Nat} {nativeReference : Term (point.native (position := position))}
  (scope : Scope (point.native (position := position)) pricing n nativeReference actor position)

def receive (site : Fin seed.source.code.sites) :=
  Production.fromRequested scope (requested (position := position) prepared point site)

theorem a_native_domain_request_is_issued_exactly_when_personally_authorized
    (site : Fin seed.source.code.sites) :
    (receive (position := position) prepared point scope site).isSome = true ↔
      Mandate.Replay.Personal actor (requested (position := position) prepared point site) := by
  rw [receive,Production.fromRequested_is_some_exactly_for_registered_personal_words,
    Prefix.own_words_are_exactly_bounded_personal_requests]
  exact ⟨And.right,fun personal => ⟨every_native_point_receives_an_original_registered_work_word (position := position) prepared point site,personal⟩⟩

def run (site : Fin seed.source.code.sites) (span : Nat) :
    Option (Reservation.Protocol (point.native (position := position)) pricing n nativeReference actor position span) :=
  (receive (position := position) prepared point scope site).map fun issued => issued.val.run span

theorem every_issued_domain_request_reaches_its_original_paid_root
    (site : Fin seed.source.code.sites) (span : Nat)
    (issued : {candidate : Production.Candidate scope // candidate.own.requested = requested (position := position) prepared point site})
    (generated : receive (position := position) prepared point scope site = some issued) :
    run (position := position) prepared point scope site span = some (issued.val.run span) ∧
    ((comparisonPoint issued.val.source).source.val.actualExecution (comparisonPoint scope).depth).submitted =
      issued.val.own.execution.output ∧
    issued.val.own.execution.consumed ++ issued.val.own.execution.residual = requested (position := position) prepared point site ∧
    (issued.val.read span).execution.origin = some issued.val.source ∧
    (issued.val.read span).learning = (issued.val.run span).endpoint ∧
    HEq ((Reservation.Runtime.facade (issued.val.run span)).readoutAt
      (Reservation.Runtime.activated (issued.val.run span)) .computation)
      ((Reservation.Runtime.activated (issued.val.run span)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Reservation.Runtime.activated (issued.val.run span)).tick.generated.wholeLedgerWriteBack
      ((Reservation.Runtime.activated (issued.val.run span)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Reservation.Runtime.activated (issued.val.run span)).current.visit.current) ∧
    (Reservation.Runtime.activated (issued.val.run span)).tick.nextCurrent =
      (Reservation.Runtime.process (issued.val.run span)).stateAt
        ((Reservation.Runtime.process (issued.val.run span)).successor
          (Reservation.Runtime.activated (issued.val.run span)).state) := by
  have native := issued.val.the_original_root_retains_the_generated_action_source_and_whole_window span
  have rooted := issued.val.the_same_original_root_consumes_the_action_reservation_and_own_next span
  refine ⟨?_,issued.val.action_is_the_exact_last_actual_source_event,
    issued.val.action_preserves_the_original_requests_and_exact_residual.trans issued.property,
    native.1,native.2.1,rooted.2.2.1,rooted.2.2.2.1,rooted.2.2.2.2⟩
  simp only [run,generated,Option.map_some]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain
