import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Payment
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Funding.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Execution
open Reparation.Actual
open private run_selects_trace from H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Word" => Script Party Good Port Technology Instrument
local notation "RawWord" => RawEvent Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument
local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument

variable (answers : ReceiptAnswers seed) (anchor : Reparation.Actual.Script Party Good Port Technology Instrument)

private abbrev roster (past : Word) :=
  ExposureGuard.bearers seed community anchor ++ ExposureGuard.bearers seed community past

set_option maxHeartbeats 800000 in
/-- The first rejected original input, carrying the exact local failure and
the checked prefix. Accounting ticks use the same ordering as material ticks. -/
inductive ProductionInputFailure : Word → Word → Type
  | refused {past : Word} {input : Proposal} {tail : Word}
      (issue : ExposureGuard.Failure (roster (community := community) (seed := seed) anchor past) answers past input) :
      ProductionInputFailure past (input :: tail)
  | damage {past : Word} {input : Proposal} {tail : Word}
      (item : Boundary.Actual.DamageAt (endAt seed past) input community)
      (present : item ∈ Boundary.Actual.damages (endAt seed past) input community) :
      ProductionInputFailure past (input :: tail)
  | later {past : Word} {input : Proposal} {tail : Word}
      (earlier : Occurrence.EligibleAt community answers anchor past input)
      (issue : ProductionInputFailure (past ++ [input]) tail) :
      ProductionInputFailure past (input :: tail)

theorem ProductionInputFailure.refutes {past word : Word}
    (failure : ProductionInputFailure (community := community) answers anchor past word) :
    ¬ Occurrence.EligibleFrom community answers anchor past word := by
  intro accepted
  induction failure with
  | refused issue => exact issue.refutes _ _ _ _ accepted.1.1
  | damage _ present => rw [accepted.1.2] at present; exact List.not_mem_nil present
  | later _ _ rejected => exact rejected accepted.2

def inspectInputs : (past word : Word) →
    ProductionInputFailure (community := community) answers anchor past word ⊕
      PLift (Occurrence.EligibleFrom community answers anchor past word)
  | _, [] => .inr ⟨trivial⟩
  | past, input :: tail =>
    match ExposureGuard.inspectAdmission (roster (community := community) (seed := seed) anchor past)
        answers past input with
    | .inl refused => .inl (.refused refused)
    | .inr accepted =>
      match h : Boundary.Actual.damages (endAt seed past) input community with
      | [] =>
        let head : Occurrence.EligibleAt community answers anchor past input := ⟨accepted.down, h⟩
        match inspectInputs (past ++ [input]) tail with
        | .inl failure => .inl (.later head failure)
        | .inr checked => .inr ⟨head, checked.down⟩
      | damage :: _ => .inl (.damage damage (h.symm ▸ List.mem_cons_self))

variable (loss : Reparation.Actual.Occurrence seed community)
  (front : Reparation.Actual.Script Party Good Port Technology Instrument)
  (body : RawEvent Party Good Port Technology Instrument)

local notation "Past" => (Occurrence.history loss ++ front)
local notation "Here" => (endAt seed Past)
local notation "Anchor" => (Occurrence.history loss)
local notation "Tail" => (primitiveScript body)
local notation "There" => (endAt seed (Occurrence.history loss ++ (front ++ Tail)))

/-- The proposed instructions have actually run at their original
positions. This applies to installing a registered technology and to both
physical legs of an exchange. -/
structure ProductionWrite : Prop where
  authorized : Conflict.Root.Authorized Here body
  trace : Trace Here body (Conflict.Root.terminal Here body)
  eligible : Occurrence.EligibleFrom community answers Anchor Past Tail

inductive ProductionDecision where
  | written (result : ProductionWrite answers loss front body)
  | authority (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (Physical.Public.interpreter (Here).native.input).rawItems (Here).raw body)
      (refused : ¬ (Here).native.input.law.Valid item.before item.request)
  | native (failure : Conflict.Root.Failure Here body)
      (refutes : ¬ Trace Here body (Conflict.Root.terminal Here body))
  | rejected (failure : ProductionInputFailure (community := community) answers Anchor Past Tail)

/-- Zero-time preparation and exchange consume the actual primitive
interpreter. The living continuation checks the period's needs separately. -/
def inspectProduction : ProductionDecision answers loss front body :=
  match Capitalism.Universal.Abolition.Material.inspectList
      (fun item => (Here).native.input.law.Valid item.before item.request)
      ((Physical.Public.interpreter (Here).native.input).rawItems (Here).raw body) with
  | .failure item original refused => .authority item original refused
  | .clear authorized =>
    match actual : run Here body with
    | .completed target trace =>
      have exactTrace : Trace Here body (Conflict.Root.terminal Here body) := by
        change Trace Here body (endAt Here Tail)
        rw [original_primitive_trace trace]
        exact trace
      match inspectInputs (community := community) answers Anchor Past Tail with
      | .inl failure => .rejected failure
      | .inr checked => .written ⟨authorized, exactTrace, checked.down⟩
    | .blocked done stopped request remaining split trace issue =>
      .native (.body done stopped request remaining split trace issue) (fun paid => by
        have completed := run_selects_trace paid
        rw [actual] at completed
        cases completed)

theorem inspectProduction_passes_iff :
    (∃ write, inspectProduction answers loss front body = .written write) ↔
      ProductionWrite answers loss front body := by
  constructor
  · rintro ⟨write, _⟩
    exact write
  · intro write
    cases inspectProduction answers loss front body with
    | written result => exact ⟨result, rfl⟩
    | authority item original refused => exact (refused (write.authorized item original)).elim
    | native _ refused => exact (refused write.trace).elim
    | rejected refused => exact ((ProductionInputFailure.refutes answers Anchor refused) write.eligible).elim

namespace ProductionWrite

variable {answers loss front body} (write : ProductionWrite answers loss front body)

include write

private theorem exact_execution :
    (Here).native.input.law.execute (Here).raw 0 body =
      (Physical.Public.interpreter (Here).native.input).execute (Here).raw 0 body :=
  PublicFunction.execute_physical_of_authorized (Here).native.input.law (Here).raw 0 body
    (fun item listed => PublicFunction.valid_physical (Here).native.input.law _ _ (write.authorized item listed))
    (fun item listed => write.authorized item listed)

theorem eligibility (earlier : Occurrence.Eligible answers loss front) :
    Occurrence.Eligible answers loss (front ++ Tail) :=
  Funding.eligible_append answers Anchor Anchor front Tail earlier write.eligible

theorem raw : (There).raw = ((Here).native.input.law.execute (Here).raw 0 body).final := by
  rw [← List.append_assoc, endAt_append]
  exact (write.trace.raw_is_the_complete_original_execution 0).trans
    (congrArg ExecutionResult.final write.exact_execution).symm

theorem inventory :
    Quantities.Execution.inventory (Here) Tail =
      (((Here).native.input.law.execute (Here).raw 0 body).items.map fun item => { item with index := 0 }) := by
  rw [primitive_inventory write.trace 0, ← write.exact_execution]

omit write in
private theorem trace_ready {first last : C} {requests : RawWord}
    (paid : Trace first requests last) (ready : Ready first) (review : ReviewAvailable first) :
    Ready last ∧ ReviewAvailable last := by
  induction paid with
  | nil => exact ⟨ready, review⟩
  | cons first request _ _ now available consents valid _ later =>
      exact later (two_actual_root_steps_pay_and_consume_the_generated_primitive first request now available consents valid).1
        (afterNative_keeps_the_available_review first request now available consents valid)

theorem ready (nonempty : body ≠ []) : ReadyEntry loss (front ++ Tail) := by
  have started := write.trace.a_nonempty_execution_starts_at_the_actual_ready_boundary nonempty
  unfold ReadyEntry
  rw [← List.append_assoc, endAt_append]
  exact trace_ready write.trace started.1 started.2

theorem origins (earlier : Occurrence.Eligible answers loss front) :
    (prefixRows loss answers (front ++ Tail)).map Prod.fst =
      (Occurrence.originState loss).stack.balances.map Prod.fst := by
  rw [Occurrence.reached_origins, Occurrence.originState_origins]
  exact Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers Anchor Anchor _
    (write.eligibility earlier)

omit write in
/-- The first paid revision changes the actual native technology. The next
material item's credit reads that technology from the revised current. -/
theorem revision_then_production_has_new_native_credit
    {revision production : Request Party Good Port Technology Instrument} {operator producer : Party}
    {technology : Technology}
    (actual : ProductionWrite answers loss front [revision, production])
    (revises : revision.operation = .revise operator technology)
    (produces : production.operation = .produce producer) :
    let revised := Conflict.Root.terminal Here [revision]
    revised.raw.technology = technology ∧
      Quantities.Execution.inventory Here (primitiveScript [revision, production]) =
        [⟨0, (Here).raw, revision⟩, ⟨0, revised.raw, production⟩] ∧
      (Here).native.input.law.actualCredit revised.raw production =
        locate producer (((Here).native.input.law.technique technology producer).outputs) := by
  let revised := Conflict.Root.terminal Here [revision]
  let physical := Physical.Public.interpreter (Here).native.input
  let law := (Here).native.input.law
  have prior := Conflict.Root.trace_before_prefix Here _ [revision] [production] actual.trace
  have raw : revised.raw = physical.step (Here).raw revision :=
    prior.raw_is_the_complete_original_execution 0
  have admitted : physical.Valid (Here).raw revision :=
    (actual.trace.every_original_instruction_has_its_actual_guards 0
      ⟨0, (Here).raw, revision⟩ List.mem_cons_self).1
  have installed : revised.raw.technology = technology := by
    rw [raw, RawLaw.step, if_pos admitted]
    simp [RawLaw.paidStep, revises]
  have second : law.Valid revised.raw production := by
    apply actual.authorized ⟨1, revised.raw, production⟩
    rw [raw]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨installed, ?_, ?_⟩
  · rw [primitive_inventory actual.trace 0, raw]
    rfl
  · rw [RawLaw.actualCredit, if_pos second, RawLaw.credit, produces, installed]

end ProductionWrite

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
