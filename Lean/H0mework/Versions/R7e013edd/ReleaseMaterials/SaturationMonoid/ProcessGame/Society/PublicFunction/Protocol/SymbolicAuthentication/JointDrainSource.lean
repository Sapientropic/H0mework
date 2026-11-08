import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliveryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainSource
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

-- Empty overdue is weaker: a fresh unconfirmed packet still has a live duty.
def Closed (state : State old instructions) : Prop :=
  state.pending = [] ∧ ∀ emission ∈ StageDuty.origins start vocabulary encoding state.history,
    TimedDuty.Confirmed start state.history vocabulary encoding law emission
instance (state : State old instructions) : Decidable (Closed old instructions start vocabulary encoding law state) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev after (entry : Attempt old instructions) :=
  OpenDeliverySource.after old instructions start vocabulary encoding law entry.state entry.command
abbrev feed (entry : Attempt old instructions) :=
  FundedRetrySource.feed old instructions start entry.state entry.command.supply
abbrev confirmations := OpenDeliverySource.confirmations old instructions start vocabulary encoding law
def gain (entry : Attempt old instructions) : Nat :=
  confirmations old instructions start vocabulary encoding law (after old instructions start vocabulary encoding law entry) -
    confirmations old instructions start vocabulary encoding law entry.state
def gains (entries : List (Attempt old instructions)) : Nat :=
  (entries.map (gain old instructions start vocabulary encoding law)).sum
def stalls (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => if (feed old instructions start entry).retired.length +
    gain old instructions start vocabulary encoding law entry = 0 then 1 else 0).sum

inductive Status where | drained | observationCut deriving DecidableEq
structure Result where
  state : State old instructions
  attempts : List (Attempt old instructions)
  arrivals : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  retired : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  status : Status

-- Query and execute the actual next input before checking this observation's queue and duties.
def run (control : Controller old instructions) : Nat → State old instructions → Result old instructions :=
  Nat.rec (fun initial => ⟨initial,[],[],[],.observationCut⟩) fun _ prior initial =>
    let entry : Attempt old instructions := ⟨initial,control initial⟩
    let next := after old instructions start vocabulary encoding law entry
    if Closed old instructions start vocabulary encoding law next then
      ⟨next,[entry],(feed old instructions start entry).arrivals,(feed old instructions start entry).retired,.drained⟩
    else
      let tail := prior next
      ⟨tail.state,entry :: tail.attempts,(feed old instructions start entry).arrivals ++ tail.arrivals,
        (feed old instructions start entry).retired ++ tail.retired,tail.status⟩

theorem run_zero (control : Controller old instructions) (initial : State old instructions) :
    run old instructions start vocabulary encoding law control 0 initial = ⟨initial,[],[],[],.observationCut⟩ := rfl
theorem run_succ (control : Controller old instructions) (count : Nat) (initial : State old instructions) :
    run old instructions start vocabulary encoding law control (count+1) initial =
      let entry : Attempt old instructions := ⟨initial,control initial⟩
      let next := after old instructions start vocabulary encoding law entry
      if Closed old instructions start vocabulary encoding law next then
        ⟨next,[entry],(feed old instructions start entry).arrivals,(feed old instructions start entry).retired,.drained⟩
      else
        let tail := run old instructions start vocabulary encoding law control count next
        ⟨tail.state,entry :: tail.attempts,(feed old instructions start entry).arrivals ++ tail.arrivals,
          (feed old instructions start entry).retired ++ tail.retired,tail.status⟩ := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainSource
