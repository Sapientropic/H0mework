import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenPrefixProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetrySource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open OpenDeliverySource (State Command Controller Attempt)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

-- The same content census as UnifiedResponse.duties, without requiring a native Bound just to select a duty.
def duties (past : List (EventHistory.Stage (code := Active old instructions))) :=
  (StageDuty.origins start vocabulary encoding past).filter fun emission =>
    decide (¬ TimedDuty.Confirmed start past vocabulary encoding law emission)
abbrev Candidate (past : List (EventHistory.Stage (code := Active old instructions))) :=
  {emission // emission ∈ duties old instructions start vocabulary encoding law past}

theorem candidate_is_actual_and_unconfirmed (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past) :
    candidate.val ∈ StageDuty.origins start vocabulary encoding past ∧
      ¬ TimedDuty.Confirmed start past vocabulary encoding law candidate.val := by
  have member := List.mem_filter.mp candidate.property
  exact ⟨member.1,of_decide_eq_true member.2⟩

abbrev waiting (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past) :=
  SilentWindow.delay (EventHistory.execute start past) candidate.val.wire.ballot.key
abbrev aligned (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past) :=
  past ++ SilentWindow.stages (waiting old instructions start vocabulary encoding law past candidate)
abbrev sent (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past)
    (supported : Event.send candidate.val.wire.ballot.key candidate.val.wire.recipient ∈ (Active old instructions).eventAlphabet) :=
  aligned old instructions start vocabulary encoding law past candidate ++
    [(TimedRetry.sending candidate.val.wire.ballot.key candidate.val.wire.recipient supported,SilentWindow.environment)]
abbrev schedule (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past)
    (supported : Event.send candidate.val.wire.ballot.key candidate.val.wire.recipient ∈ (Active old instructions).eventAlphabet)
    (network : Opponent (Active old instructions)) :=
  sent old instructions start vocabulary encoding law past candidate supported ++ [(SilentWindow.quiet,network)]

structure Ready (past : List (EventHistory.Stage (code := Active old instructions))) where
  private mk ::
  candidate : Candidate old instructions start vocabulary encoding law past
  supported : Event.send candidate.val.wire.ballot.key candidate.val.wire.recipient ∈ (Active old instructions).eventAlphabet
  fuel : waiting old instructions start vocabulary encoding law past candidate + 2 ≤ (EventStep.seed (EventHistory.execute start past)).remaining
  wire : StageTransport.Wire (code := Active old instructions)
  issued : StageTransport.issuedAt vocabulary encoding start
    (sent old instructions start vocabulary encoding law past candidate supported)
    (aligned old instructions start vocabulary encoding law past candidate).length = some wire
  same_content : StageDuty.content wire = StageDuty.content candidate.val.wire
  deliverable : Event.deliver wire.serial ∈ (Active old instructions).eventAlphabet
  received : StageQueueProgress.readyAt vocabulary encoding law start
    (schedule old instructions start vocabulary encoding law past candidate supported (TimedRetry.delivery wire.serial deliverable))
    candidate.val.wire.recipient ((aligned old instructions start vocabulary encoding law past candidate).length+1) = some wire

inductive Plan (past : List (EventHistory.Stage (code := Active old instructions))) where
  | idle
  | blocked (reason : TimedRetry.Obstruction)
  | ready (answer : Ready old instructions start vocabulary encoding law past)

-- Feasibility is computed at this source. Only actual callback receipts classify the executed attempt.
def produce (past : List (EventHistory.Stage (code := Active old instructions))) :
    Plan old instructions start vocabulary encoding law past :=
  match (duties old instructions start vocabulary encoding law past).attach.head? with
  | none => .idle
  | some candidate =>
    if supported : Event.send candidate.val.wire.ballot.key candidate.val.wire.recipient ∈ (Active old instructions).eventAlphabet then
    if fuel : waiting old instructions start vocabulary encoding law past candidate+2 ≤ (EventStep.seed (EventHistory.execute start past)).remaining then
      match issued : StageTransport.issuedAt vocabulary encoding start
          (sent old instructions start vocabulary encoding law past candidate supported)
          (aligned old instructions start vocabulary encoding law past candidate).length with
      | none => .blocked .noAuthenticatedSend
      | some wire =>
        if same : StageDuty.content wire = StageDuty.content candidate.val.wire then
        if deliverable : Event.deliver wire.serial ∈ (Active old instructions).eventAlphabet then
        if received : StageQueueProgress.readyAt vocabulary encoding law start
            (schedule old instructions start vocabulary encoding law past candidate supported (TimedRetry.delivery wire.serial deliverable))
            candidate.val.wire.recipient ((aligned old instructions start vocabulary encoding law past candidate).length+1) = some wire then
          .ready ⟨candidate,supported,fuel,wire,issued,same,deliverable,received⟩
        else .blocked .reception
        else .blocked .unsupportedDelivery
        else .blocked .changedContent
    else .blocked .exhausted
    else .blocked .unsupportedSend

abbrev prepared (state : State old instructions) (command : Command old instructions) :=
  FundedRetrySource.prepared old instructions start state command.supply
abbrev plan (state : State old instructions) (command : Command old instructions) :=
  produce old instructions start vocabulary encoding law (prepared old instructions start state command)
def after (state : State old instructions) (command : Command old instructions) : State old instructions :=
  ⟨match plan old instructions start vocabulary encoding law state command with
    | .ready answer => schedule old instructions start vocabulary encoding law _ answer.candidate answer.supported command.network
    | _ => prepared old instructions start state command,
    (FundedRetrySource.supplied old instructions start state command.supply).pending⟩
def kind (entry : Attempt old instructions) : OpenDeliverySource.Kind :=
  match plan old instructions start vocabulary encoding law entry.state entry.command with
  | .idle => .idle
  | .blocked _ => .blocked
  | .ready answer => OpenDeliverySource.confirmationKind old instructions start vocabulary encoding law
      (schedule old instructions start vocabulary encoding law _ answer.candidate answer.supported entry.command.network) answer.candidate.val

abbrev confirmations := OpenDeliverySource.confirmations old instructions start vocabulary encoding law
def confirmedCount (entries : List (Attempt old instructions)) :=
  (entries.map fun entry => if kind old instructions start vocabulary encoding law entry = .confirmed then 1 else 0).sum
def obstructionCount (entries : List (Attempt old instructions)) :=
  (entries.map fun entry => if kind old instructions start vocabulary encoding law entry = .blocked ∨
    kind old instructions start vocabulary encoding law entry = .unconfirmed then 1 else 0).sum

def run (initial : State old instructions) (control : Controller old instructions) : Nat → OpenDeliverySource.Result old instructions :=
  Nat.rec ⟨initial,[],[],[]⟩ fun _ previous =>
    let command := control previous.state
    ⟨after old instructions start vocabulary encoding law previous.state command,
      previous.attempts ++ [⟨previous.state,command⟩],
      previous.arrivals ++ (FundedRetrySource.feed old instructions start previous.state command.supply).arrivals,
      previous.retired ++ (FundedRetrySource.feed old instructions start previous.state command.supply).retired⟩
theorem run_zero (initial : State old instructions) (control : Controller old instructions) :
    run old instructions start vocabulary encoding law initial control 0 = ⟨initial,[],[],[]⟩ := rfl
theorem run_succ (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    run old instructions start vocabulary encoding law initial control (count+1) =
      let previous := run old instructions start vocabulary encoding law initial control count
      let command := control previous.state
      ⟨after old instructions start vocabulary encoding law previous.state command,
        previous.attempts ++ [⟨previous.state,command⟩],
        previous.arrivals ++ (FundedRetrySource.feed old instructions start previous.state command.supply).arrivals,
        previous.retired ++ (FundedRetrySource.feed old instructions start previous.state command.supply).retired⟩ := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetrySource
