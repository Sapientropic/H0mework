import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Receipt
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal.Tail

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private def ruleDecidableEq : DecidableEq (Prefix.Rule code) := fun first second =>
  decidable_of_iff (∀ key : code.Key,
    first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key) ∧
    (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val) (by
    constructor
    · intro same
      have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
      have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
      cases first
      cases second
      cases work
      cases events
      rfl
    · intro same
      subst second
      exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Prefix.Rule code) := ruleDecidableEq

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)


abbrev start (announcements : List (Prefix.Rule model.source.code)) := quotas.length+announcements.length
abbrev owner (index : Nat) := Distributed.Recall.Information.Agency.ownerAt model.source.code point.point.ownerStart
  ((PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed point.point).history.length+index)

theorem the_registered_clock_is_the_actual_prefix_clock (past : List (Prefix.Rule model.source.code)) :
    Distributed.Recall.Information.Agency.ownerAt model.source.code
      (Window.Observed.Transcript.actualView past point rival).point.ownerStart
      (PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed
        (Window.Observed.Transcript.actualView past point rival).point).history.length = owner model point past.length := by
  have ownerKept (rules : List (Prefix.Rule model.source.code)) (view : View (code := model.source.code)) :
      (Window.Observed.Transcript.actualView rules view rival).point.ownerStart = view.point.ownerStart := by
    induction rules generalizing view with
    | nil => rfl
    | cons rule rest ih => exact ih (Evidence.after view rule rival)
  have size (rules : List (Prefix.Rule model.source.code)) (view : View (code := model.source.code)) :
      (PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed
        (Window.Observed.Transcript.actualView rules view rival).point).history.length =
      (PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed view.point).history.length+rules.length := by
    induction rules generalizing view with
    | nil => rfl
    | cons rule rest ih =>
        change (PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed
          (Window.Observed.Transcript.actualView rest (Evidence.after view rule rival) rival).point).history.length = _
        rw [ih]
        change (PublicFunction.Protocol.SymbolicAuthentication.EventStep.seed (view.point.after rule rival)).history.length+rest.length = _
        rw [PublicFunction.Protocol.SymbolicAuthentication.EventStep.actual_next_state]
        simp only [history_keeps_every_actual_word,List.length_append,List.length_cons,List.length_nil]
        omega
  rw [ownerKept,size]

/-- Fee marks are separated by a complete learning stage. Later marks use the
same original ownership clock, rather than a future success table. -/
def FeeAt (announcements : List (Prefix.Rule model.source.code)) (index : Nat) : Prop :=
  start model quotas announcements ≤ index ∧ index+1 < Deployment.actualHorizon model point ∧
  index+1 < horizon domain ∧ (index-start model quotas announcements)%2 = 0 ∧
  (index=start model quotas announcements ∨ owner model point index = some receiver)
instance (announcements : List (Prefix.Rule model.source.code)) (index : Nat) :
    Decidable (FeeAt model domain receiver quotas point announcements index) := by unfold FeeAt;infer_instance

theorem fee_marks_leave_the_learning_stage_open
    (announcements : List (Prefix.Rule model.source.code)) (index : Nat)
    (here : FeeAt model domain receiver quotas point announcements index) :
    ¬ FeeAt model domain receiver quotas point announcements (index+1) := by
  intro next
  have first := here.2.2.2.1
  have second := next.2.2.2.1
  have later := here.1
  omega

def SenderMatches (send rule : Prefix.Rule model.source.code) : Prop :=
  ∀ signal : Fin model.source.code.signals,
    rule.work.val (worker,signal) (model.source.code.key_mem _) = send.work.val (worker,signal) (model.source.code.key_mem _) ∧
    (rule.events (worker,signal) (model.source.code.key_mem _)).val = (send.events (worker,signal) (model.source.code.key_mem _)).val
instance (send rule : Prefix.Rule model.source.code) : Decidable (SenderMatches model worker send rule) := by unfold SenderMatches;infer_instance

def checkAt (send : Prefix.Rule model.source.code) (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) (index : Nat) : Bool :=
  if index < start model quotas announcements then true
  else if FeeAt model domain receiver quotas point announcements index then
    decide (candidate.protocol.at original index = Reservation.fee model original receiver quote)
  else decide (candidate.protocol.at original index ≠ Reservation.fee model original receiver quote ∧
    (owner model point index = some worker → SenderMatches model worker send (candidate.protocol.at original index)))

def profile (send : Prefix.Rule model.source.code) (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) : Bool :=
  (List.range (horizon domain)).all (checkAt model domain original reference worker receiver quote quotas point send announcements candidate)

def eligible (send : Prefix.Rule model.source.code) (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) : Bool :=
  Reservation.eligible model domain original reference worker receiver quote quotas announcements candidate &&
    profile model domain original reference worker receiver quote quotas point send announcements candidate

private theorem publication_prefix
    (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference)
    (selected : Reservation.eligible model domain original reference worker receiver quote quotas announcements candidate = true) :
    Plan.eligible model domain original reference worker quote quotas announcements candidate = true := by
  apply (Plan.eligible_iff model domain original reference worker quote quotas announcements candidate).mpr
  have retained := (Reservation.eligible_iff model domain original reference worker receiver quote quotas announcements candidate).mp selected
  have earlier := congrArg (List.take (quotas.length+announcements.length)) retained
  rw [List.take_take,Nat.min_eq_left (Nat.le_succ _)] at earlier
  have size : (reserved model original worker quote quotas ++ announcements).length = quotas.length+announcements.length := by simp [Segmented.reserved]
  unfold Reservation.reservedBlock at earlier
  rw [←size,List.take_append_of_le_length (Nat.le_refl _),List.take_length] at earlier
  simpa only [size] using earlier

structure Selection where
  reservation : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal
  send : Prefix.Rule model.source.code
  registeredSend : Plan.sendRule worker receiver = some send
  distinct : worker ≠ receiver
  continued : profile model domain original reference worker receiver quote quotas point send reservation.plan.announcements reservation.plan.choice.policy = true

inductive Blocked where
  | unsupportedFee (outside : Charge.fee quote ∉ words model.source.code.actions model.source.code.actionLimit)
  | sameSite (same : worker = receiver)
  | unsupportedSend (outside : Distributed.Event.send worker receiver ∉ model.source.code.eventAlphabet)
  | actualWindow (send : Prefix.Rule model.source.code) (registered : Plan.sendRule worker receiver = some send)
      (short : ¬ quotas.length+(List.replicate slots send).length+1 < Deployment.actualHorizon model point)
  | domainWindow (send : Prefix.Rule model.source.code) (registered : Plan.sendRule worker receiver = some send)
      (short : ¬ quotas.length+(List.replicate slots send).length+1 < horizon domain)
  | notArrived (missing : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal = none)
  | unfinished (scanned : Scan model domain original reference worker quote quotas rival point none quotas)
      (missing : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal = some (scanned,none))
  | noRenewalChoice (send : Prefix.Rule model.source.code) (registered : Plan.sendRule worker receiver = some send)
      (finished : Finished model domain original reference worker quote quotas)
      (rejected : ∀ choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference,
        eligible model domain original reference worker receiver quote quotas point send (List.replicate slots send) choice.policy ≠ true)

inductive Result where
  | blocked (reason : Blocked model domain original reference worker receiver quote quotas slots point rival ordinal)
  | selected (selection : Selection model domain original reference worker receiver quote quotas slots point rival ordinal)

def generate : Result model domain original reference worker receiver quote quotas slots point rival ordinal :=
  if supported : Charge.fee quote ∈ words model.source.code.actions model.source.code.actionLimit then
    if same : worker = receiver then .blocked (.sameSite same)
    else match registeredSend : Plan.sendRule (code := model.source.code) worker receiver with
    | none => .blocked (.unsupportedSend (Plan.unavailable_send_is_outside_the_original_source worker receiver registeredSend))
    | some send =>
      let announcements := List.replicate slots send
      if actualRoom : quotas.length+announcements.length+1 < Deployment.actualHorizon model point then
        if domainRoom : quotas.length+announcements.length+1 < horizon domain then
          match arrived : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal with
          | none => .blocked (.notArrived arrived)
          | some (scanned,none) => .blocked (.unfinished scanned arrived)
          | some (scanned,some finished) =>
            match picked : Constrained.choose model domain original (reserved model original worker quote quotas) reference
                (eligible model domain original reference worker receiver quote quotas point send announcements) finished.work finished.complete with
            | none => .blocked (.noRenewalChoice send registeredSend finished
                (Constrained.absence_rejects_every_eligible_global_choice model domain original (reserved model original worker quote quotas) reference
                  (eligible model domain original reference worker receiver quote quotas point send announcements) finished.work finished.complete picked))
            | some chosen =>
              have both : Reservation.eligible model domain original reference worker receiver quote quotas announcements chosen.val.policy = true ∧
                  profile model domain original reference worker receiver quote quotas point send announcements chosen.val.policy = true := by
                simpa only [eligible,Bool.and_eq_true_iff] using chosen.property
              .selected ⟨⟨⟨announcements,by simp only [Plan.layout,registeredSend,Option.map_some,announcements],by omega,
                  scanned,finished,arrived,chosen.val,
                  publication_prefix model domain original reference worker receiver quote quotas announcements chosen.val.policy both.1⟩,
                supported,actualRoom,domainRoom,both.1⟩,send,registeredSend,same,both.2⟩
        else .blocked (.domainWindow send registeredSend domainRoom)
      else .blocked (.actualWindow send registeredSend actualRoom)
  else .blocked (.unsupportedFee supported)

def select : Option (Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :=
  match generate model domain original reference worker receiver quote quotas slots point rival ordinal with
  | .blocked _ => none
  | .selected selection => some selection

def obstruction (absent : select model domain original reference worker receiver quote quotas slots point rival ordinal = none) :
    Blocked model domain original reference worker receiver quote quotas slots point rival ordinal :=
  match made : generate model domain original reference worker receiver quote quotas slots point rival ordinal with
  | .blocked reason => reason
  | .selected selection => False.elim (by simp only [select,made] at absent;cases absent)

variable (selected : Selection model domain original reference worker receiver quote quotas slots point rival ordinal)

theorem every_registered_future_fee_is_in_the_original_complete_plan
    (index : Nat) (fee : FeeAt model domain receiver quotas point selected.reservation.plan.announcements index) :
    selected.reservation.plan.choice.policy.protocol.at original index = Reservation.fee model original receiver quote := by
  have entry := List.all_eq_true.mp selected.continued index (List.mem_range.mpr (by have bound := fee.2.2.1;omega))
  have later : ¬ index < start model quotas selected.reservation.plan.announcements := by have bound := fee.1;omega
  simpa only [checkAt,if_neg later,if_pos fee,decide_eq_true_eq] using entry

theorem every_other_future_slot_retains_its_registered_sender
    (index : Nat) (inside : index < horizon domain)
    (later : start model quotas selected.reservation.plan.announcements ≤ index)
    (nonfee : ¬ FeeAt model domain receiver quotas point selected.reservation.plan.announcements index) :
    selected.reservation.plan.choice.policy.protocol.at original index ≠ Reservation.fee model original receiver quote ∧
      (owner model point index = some worker → SenderMatches model worker selected.send (selected.reservation.plan.choice.policy.protocol.at original index)) := by
  have entry := List.all_eq_true.mp selected.continued index (List.mem_range.mpr inside)
  simpa only [checkAt,if_neg (Nat.not_lt.mpr later),if_neg nonfee,decide_eq_true_eq] using entry

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal
