import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Installation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Source

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
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


abbrev fee := Charge.feeRule quote model receiver original
abbrev reservedBlock (announcements : List (Prefix.Rule model.source.code)) :=
  reserved model original worker quote quotas ++ announcements ++ [fee model original receiver quote]

def eligible (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) : Bool :=
  decide (candidate.protocol.controls.take (quotas.length+announcements.length+1) =
    reservedBlock model original worker receiver quote quotas announcements)

theorem eligible_iff (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) :
    eligible model domain original reference worker receiver quote quotas announcements candidate = true ↔
      candidate.protocol.controls.take (quotas.length+announcements.length+1) =
        reservedBlock model original worker receiver quote quotas announcements := by
  simp only [eligible,decide_eq_true_eq]

structure Selection where
  plan : Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal
  supported : Charge.fee quote ∈ words model.source.code.actions model.source.code.actionLimit
  actualRoom : quotas.length+plan.announcements.length+1 < Deployment.actualHorizon model point
  domainRoom : quotas.length+plan.announcements.length+1 < horizon domain
  reservedNext : eligible model domain original reference worker receiver quote quotas plan.announcements plan.choice.policy = true

private theorem publication_prefix
    (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference)
    (selected : eligible model domain original reference worker receiver quote quotas announcements candidate = true) :
    Plan.eligible model domain original reference worker quote quotas announcements candidate = true := by
  apply (Plan.eligible_iff model domain original reference worker quote quotas announcements candidate).mpr
  have retained := (eligible_iff model domain original reference worker receiver quote quotas announcements candidate).mp selected
  have earlier := congrArg (List.take (quotas.length+announcements.length)) retained
  rw [List.take_take,Nat.min_eq_left (Nat.le_succ _)] at earlier
  have size : (reserved model original worker quote quotas ++ announcements).length = quotas.length+announcements.length := by simp [Segmented.reserved]
  unfold reservedBlock at earlier
  rw [←size,List.take_append_of_le_length (Nat.le_refl _),List.take_length] at earlier
  simpa only [size] using earlier

/-- Read the already-paid complete cache. Eligibility restricts the layout of the
result, while maximality still compares the entire original accepted pool. -/
def select : Option (Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :=
  if supported : Charge.fee quote ∈ words model.source.code.actions model.source.code.actionLimit then
    match registered : Plan.layout model worker receiver slots with
    | none => none
    | some announcements =>
      if actualRoom : quotas.length+announcements.length+1 < Deployment.actualHorizon model point then
        if domainRoom : quotas.length+announcements.length+1 < horizon domain then
          match arrived : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal with
          | some (scanned,some finished) =>
            match Constrained.choose model domain original (reserved model original worker quote quotas) reference
              (eligible model domain original reference worker receiver quote quotas announcements) finished.work finished.complete with
            | none => none
            | some picked => some ⟨⟨announcements,registered,by omega,scanned,finished,arrived,picked.val,
                publication_prefix model domain original reference worker receiver quote quotas announcements picked.val.policy picked.property⟩,
                supported,actualRoom,domainRoom,picked.property⟩
          | _ => none
        else none
      else none
  else none

inductive Blocked where
  | unsupportedFee (outside : Charge.fee quote ∉ words model.source.code.actions model.source.code.actionLimit)
  | unsupportedSend (outside : Distributed.Event.send worker receiver ∉ model.source.code.eventAlphabet)
  | actualWindow (announcements : List (Prefix.Rule model.source.code))
      (registered : Plan.layout model worker receiver slots = some announcements)
      (short : ¬ quotas.length+announcements.length+1 < Deployment.actualHorizon model point)
  | domainWindow (announcements : List (Prefix.Rule model.source.code))
      (registered : Plan.layout model worker receiver slots = some announcements)
      (short : ¬ quotas.length+announcements.length+1 < horizon domain)
  | notArrived (missing : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal = none)
  | unfinished (scanned : Scan model domain original reference worker quote quotas rival point none quotas)
      (missing : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal = some (scanned,none))
  | noEligibleGlobalChoice (announcements : List (Prefix.Rule model.source.code))
      (registered : Plan.layout model worker receiver slots = some announcements)
      (finished : Finished model domain original reference worker quote quotas)
      (rejected : ∀ choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference,
        eligible model domain original reference worker receiver quote quotas announcements choice.policy ≠ true)

def obstruction (absent : select model domain original reference worker receiver quote quotas slots point rival ordinal = none) :
    Blocked model domain original reference worker receiver quote quotas slots point rival ordinal := by
  unfold select at absent
  split at absent
  · split at absent
    · rename_i registered
      apply Blocked.unsupportedSend
      apply Plan.unavailable_send_is_outside_the_original_source
      cases generated : Plan.sendRule (code := model.source.code) worker receiver with
      | none => rfl
      | some protocol => simp only [Plan.layout,generated,Option.map_some] at registered;cases registered
    · rename_i announcements registered
      split at absent
      · split at absent
        · split at absent
          · rename_i scanned finished arrived
            split at absent
            · rename_i noChoice
              exact .noEligibleGlobalChoice announcements registered finished
                (Constrained.absence_rejects_every_eligible_global_choice model domain original (reserved model original worker quote quotas) reference
                  (eligible model domain original reference worker receiver quote quotas announcements) finished.work finished.complete noChoice)
            · cases absent
          · rename_i missing
            cases observed : Segmented.Runtime.read model domain original reference worker quote quotas point rival ordinal with
            | none => exact .notArrived observed
            | some pair =>
              rcases pair with ⟨scanned,result⟩
              cases result with
              | none => exact .unfinished scanned observed
              | some finished => exact False.elim (missing scanned finished observed)
        · exact .domainWindow announcements registered (by assumption)
      · exact .actualWindow announcements registered (by assumption)
  · exact .unsupportedFee (by assumption)

def future : List (Prefix.Rule model.source.code) :=
  match select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => []
  | some selected => (Deployment.completeControls model domain original point selected.plan.choice.policy.protocol).drop quotas.length

def cutPoint (count : Nat) := Splice.install
  (Deployment.paidFinal model domain original reference worker quote quotas point rival) rival
  ((future model domain original reference worker receiver quote quotas slots point rival ordinal).take count)

abbrev full := cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal
  (Deployment.actualHorizon model point)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation
