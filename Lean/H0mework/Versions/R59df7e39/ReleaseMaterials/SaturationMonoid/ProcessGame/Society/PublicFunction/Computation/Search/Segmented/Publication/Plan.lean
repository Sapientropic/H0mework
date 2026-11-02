import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Constrained
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Deployment

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Plan
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

def sendRule (sender receiver : Fin code.sites) : Option (Prefix.Rule code) :=
  if supported : Distributed.Event.send sender receiver ∈ code.eventAlphabet then
    let send : LocalMove code sender := ⟨some ⟨.send sender receiver,supported⟩, by
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨⟨.send sender receiver,supported⟩,?_,rfl⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_attach _ _,by simp⟩⟩
    some {work := ⟨fun _ _ => [],by
            apply code.every_local_policy_is_enumerated
            intro key inside
            exact (mem_words_iff _ _ _).mpr (by simp)⟩,
          events := fun key _ => if own : key.1 = sender then own.symm ▸ send else ⟨none,List.mem_cons_self⟩}
  else none

theorem unavailable_send_is_outside_the_original_source (sender receiver : Fin code.sites)
    (absent : sendRule sender receiver = none) : .send sender receiver ∉ code.eventAlphabet := by
  unfold sendRule at absent
  split at absent
  · cases absent
  · assumption

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)

abbrev layout : Option (List (Prefix.Rule model.source.code)) :=
  (sendRule worker receiver).map (List.replicate slots)

def eligible (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) : Bool :=
  decide (candidate.protocol.controls.take (quotas.length+announcements.length) =
    reserved model original worker quote quotas ++ announcements)

theorem eligible_iff (announcements : List (Prefix.Rule model.source.code))
    (candidate : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference) :
    eligible model domain original reference worker quote quotas announcements candidate = true ↔
      candidate.protocol.controls.take (quotas.length+announcements.length) =
        reserved model original worker quote quotas ++ announcements := by
  simp only [eligible,decide_eq_true_eq]

structure Selection where
  announcements : List (Prefix.Rule model.source.code)
  registered : layout model worker receiver slots = some announcements
  within : quotas.length + announcements.length ≤ Deployment.actualHorizon model point
  execution : Scan model domain original reference worker quote quotas rival point none quotas
  finished : Finished model domain original reference worker quote quotas
  arrived : Runtime.read model domain original reference worker quote quotas point rival ordinal = some (execution,some finished)
  choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference
  publicationPrefix : eligible model domain original reference worker quote quotas announcements choice.policy = true

/-- The original full comparison pool is retained. The communication rules are
already inside each accepted programme's original complete evaluation. -/
def select : Option (Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :=
  match registered : layout model worker receiver slots with
  | none => none
  | some announcements =>
    if within : quotas.length+announcements.length ≤ Deployment.actualHorizon model point then
      match arrived : Runtime.read model domain original reference worker quote quotas point rival ordinal with
      | some (scanned,some finished) =>
        match Constrained.choose model domain original (reserved model original worker quote quotas) reference
          (eligible model domain original reference worker quote quotas announcements) finished.work finished.complete with
        | none => none
        | some picked => some ⟨announcements,registered,within,scanned,finished,arrived,picked.val,picked.property⟩
      | _ => none
    else none

inductive Blocked where
  | unsupported (outside : Distributed.Event.send worker receiver ∉ model.source.code.eventAlphabet)
  | insufficientWindow (announcements : List (Prefix.Rule model.source.code))
      (registered : layout model worker receiver slots = some announcements)
      (short : ¬ quotas.length+announcements.length ≤ Deployment.actualHorizon model point)
  | notArrived (missing : Runtime.read model domain original reference worker quote quotas point rival ordinal = none)
  | unfinished (execution : Scan model domain original reference worker quote quotas rival point none quotas)
      (missing : Runtime.read model domain original reference worker quote quotas point rival ordinal = some (execution,none))
  | noEligibleGlobalChoice (announcements : List (Prefix.Rule model.source.code))
      (registered : layout model worker receiver slots = some announcements)
      (within : quotas.length+announcements.length ≤ Deployment.actualHorizon model point)
      (execution : Scan model domain original reference worker quote quotas rival point none quotas)
      (finished : Finished model domain original reference worker quote quotas)
      (arrived : Runtime.read model domain original reference worker quote quotas point rival ordinal = some (execution,some finished))
      (rejected : ∀ choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference,
        eligible model domain original reference worker quote quotas announcements choice.policy ≠ true)

def obstruction (absent : select model domain original reference worker receiver quote quotas slots point rival ordinal = none) :
    Blocked model domain original reference worker receiver quote quotas slots point rival ordinal := by
  unfold select at absent
  split at absent
  · rename_i registered
    apply Blocked.unsupported
    apply unavailable_send_is_outside_the_original_source
    cases generated : sendRule (code := model.source.code) worker receiver with
    | none => rfl
    | some protocol => simp only [layout,generated,Option.map_some] at registered;cases registered
  · rename_i announcements registered
    split at absent
    · rename_i within
      split at absent
      · rename_i scanned finished arrived
        split at absent
        · rename_i noChoice
          exact .noEligibleGlobalChoice announcements registered within scanned finished arrived
            (Constrained.absence_rejects_every_eligible_global_choice model domain original (reserved model original worker quote quotas) reference
              (eligible model domain original reference worker quote quotas announcements) finished.work finished.complete noChoice)
        · cases absent
      · rename_i missing
        cases observed : Runtime.read model domain original reference worker quote quotas point rival ordinal with
        | none => exact .notArrived observed
        | some pair =>
          rcases pair with ⟨scanned,result⟩
          cases result with
          | none => exact .unfinished scanned observed
          | some finished => exact False.elim (missing scanned finished observed)
    · exact .insufficientWindow announcements registered (by assumption)

def future : List (Prefix.Rule model.source.code) :=
  match select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => []
  | some selected => (Deployment.completeControls model domain original point selected.choice.policy.protocol).drop quotas.length

def cutPoint (count : Nat) := Splice.install
  (Deployment.paidFinal model domain original reference worker quote quotas point rival) rival
  ((future model domain original reference worker receiver quote quotas slots point rival ordinal).take count)

abbrev full := cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal
  (Deployment.actualHorizon model point)

variable (selected : Selection model domain original reference worker receiver quote quotas slots point rival ordinal)
  (made : select model domain original reference worker receiver quote quotas slots point rival ordinal = some selected)

theorem selected_full_contract : Prefix.Contract model domain original (reserved model original worker quote quotas) reference
    (.selected selected.choice) := Prefix.every_generated_outcome_has_the_complete_future_contract model domain original (reserved model original worker quote quotas) reference (.selected selected.choice)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Plan
