import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventFundedEntry

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventMemorySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Effects carry the actual submitted word or paid packet, never a ready-state witness.
inductive Effect (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  | idle
  | action (site : Fin code.sites) (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  | send (sender recipient : Fin code.sites) (reading : Fin code.signals)
  | delivery (recipient sender : Fin code.sites) (reading : Fin code.signals)

def apply (effect : Effect code) (memory : Fin code.sites → Fin code.signals) : Fin code.sites → Fin code.signals :=
  match effect with
  | .idle => memory
  | .action worker word => fun site => if site = worker then code.afterAction worker (memory site) word else memory site
  | .send sender recipient reading => fun site => if site = sender then code.afterSend sender recipient (memory site) reading else memory site
  | .delivery recipient sender reading => fun site => if site = recipient then code.afterDelivery recipient sender (memory site) reading else memory site

def ofEvent (policy : code.Policy)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (frame : code.Frame) :
    Event Party Good Port (Mandate.State Party Technology) Instrument code.sites → Effect code
  | .adversary _ => .idle
  | .activate worker => .action worker (code.action policy worker (frame.inbox worker))
  | .send sender recipient =>
      if ∀ item ∈ code.law.rawItems (code.rawAt current frame) (code.sendCost sender recipient), code.law.Valid item.before item.request then
        .send sender recipient (code.readLocal sender (code.snapshot sender (code.rawAt current frame))) else .idle
  | .deliver address => match frame.sent[address]? with
      | none => .idle
      | some packet =>
          if ∀ item ∈ code.law.rawItems (code.rawAt current frame) (code.deliveryCost packet.recipient), code.law.Valid item.before item.request then
            .delivery packet.recipient packet.sender packet.signal else .idle

omit [DecidableEq Port] [DecidableEq Technology] in
theorem source_effect_is_the_exact_local_update (policy : code.Policy)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (frame : code.Frame)
    (event : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites) :
    apply (ofEvent policy current frame event) frame.inbox = (code.step policy current frame event).inbox := by
  funext site
  cases event with
  | adversary request => rfl
  | activate worker => simp only [ofEvent, apply, Code.step]; split <;> simp_all
  | send sender recipient =>
    simp only [ofEvent, Code.step, decide_eq_true_eq]
    split <;> simp_all [apply]
  | deliver address =>
    simp only [ofEvent, Code.step]
    split <;> simp_all only [apply, decide_eq_true_eq]
    split <;> simp_all

def effect (cursor : Cursor code) (stage : EventHistory.Stage (code := code)) : Effect code :=
  match decision code (EventStep.applied cursor stage.1 stage.2) (EventStep.seed cursor) with
  | none => .idle
  | some event => ofEvent stage.1.work.val (EventStep.seed cursor).current
      {(EventStep.seed cursor).frame with word := []} event.val

theorem actual_stage_generates_its_exact_memory_effect (cursor : Cursor code)
    (stage : EventHistory.Stage (code := code)) :
    apply (effect cursor stage) (EventStep.seed cursor).frame.inbox =
      (EventStep.seed (cursor.after stage.1 stage.2)).frame.inbox := by
  rw [EventStep.actual_next_state]
  cases chosen : decision code (EventStep.applied cursor stage.1 stage.2) (EventStep.seed cursor) with
  | none => simp only [effect, chosen, apply, Reaction.Feedback.advance]
  | some event =>
    simpa only [effect, chosen, Reaction.Feedback.advance, stepLocal] using
      source_effect_is_the_exact_local_update stage.1.work.val (EventStep.seed cursor).current
        {(EventStep.seed cursor).frame with word := []} event.val

def replay (cursor : Cursor code) (memory : Fin code.sites → Fin code.signals) :
    List (EventHistory.Stage (code := code)) → (Fin code.sites → Fin code.signals)
  | [] => memory
  | stage :: tail => replay (cursor.after stage.1 stage.2) (apply (effect cursor stage) memory) tail

theorem source_events_generate_the_complete_actual_local_memory (cursor : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) :
    replay cursor (EventStep.seed cursor).frame.inbox stages =
      (EventStep.seed (EventHistory.execute cursor stages)).frame.inbox := by
  induction stages generalizing cursor with
  | nil => rfl
  | cons stage tail ih => rw [replay, actual_stage_generates_its_exact_memory_effect]; exact ih _

theorem regained_readiness_requires_an_actual_nonidle_source_effect (cursor : Cursor code)
    (stage : EventHistory.Stage (code := code)) (site : Fin code.sites)
    (spent : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = false)
    (regained : code.memoryReady ((EventStep.seed (cursor.after stage.1 stage.2)).frame.inbox site) = true) :
    effect cursor stage ≠ .idle := by
  intro idle
  have same := actual_stage_generates_its_exact_memory_effect cursor stage
  rw [idle] at same
  change (EventStep.seed cursor).frame.inbox = _ at same
  rw [← same, spent] at regained
  contradiction

def ownedReady (cursor : Cursor code) (memory : Fin code.sites → Fin code.signals) : Bool :=
  match Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
  | none => true
  | some site => code.memoryReady (memory site)

-- Unready intervals are allowed between owned cuts; only actual admitted effects repair them.
def inspect (cursor : Cursor code) (memory : Fin code.sites → Fin code.signals) :
    List (EventHistory.Stage (code := code)) → Bool
  | [] => true
  | stage :: tail => ownedReady cursor memory &&
      inspect (cursor.after stage.1 stage.2) (apply (effect cursor stage) memory) tail

theorem actual_effects_generate_memory_at_every_owned_cut (cursor : Cursor code)
    (stages : List (EventHistory.Stage (code := code)))
    (checked : inspect cursor (EventStep.seed cursor).frame.inbox stages = true)
    (n : Nat) (inside : n < stages.length) (receiver : Fin code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt code (EventHistory.execute cursor (stages.take n)).ownerStart
      (EventStep.seed (EventHistory.execute cursor (stages.take n))).history.length = some receiver) :
    code.memoryReady ((EventStep.seed (EventHistory.execute cursor (stages.take n))).frame.inbox receiver) = true := by
  induction stages generalizing cursor n with
  | nil => simp only [List.length_nil] at inside; omega
  | cons stage tail ih =>
    have gates := Bool.and_eq_true_iff.mp checked
    cases n with
    | zero =>
      change Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart
        (EventStep.seed cursor).history.length = some receiver at owned
      change code.memoryReady ((EventStep.seed cursor).frame.inbox receiver) = true
      simpa only [ownedReady, owned] using gates.1
    | succ n =>
      rw [actual_stage_generates_its_exact_memory_effect] at gates
      exact ih (cursor.after stage.1 stage.2) gates.2 n
        (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside) owned

theorem failed_replay_names_an_actual_owned_memory_obstruction (cursor : Cursor code)
    (stages : List (EventHistory.Stage (code := code)))
    (failed : inspect cursor (EventStep.seed cursor).frame.inbox stages = false) :
    ∃ n : Fin stages.length, ∃ receiver : Fin code.sites,
      Distributed.Recall.Information.Agency.ownerAt code (EventHistory.execute cursor (stages.take n.val)).ownerStart
        (EventStep.seed (EventHistory.execute cursor (stages.take n.val))).history.length = some receiver ∧
      code.memoryReady ((EventStep.seed (EventHistory.execute cursor (stages.take n.val))).frame.inbox receiver) = false := by
  induction stages generalizing cursor with
  | nil => contradiction
  | cons stage tail ih =>
    by_cases ready : ownedReady cursor (EventStep.seed cursor).frame.inbox = true
    · have next : inspect (cursor.after stage.1 stage.2)
          (EventStep.seed (cursor.after stage.1 stage.2)).frame.inbox tail = false := by
        rw [inspect, ready, Bool.true_and, actual_stage_generates_its_exact_memory_effect] at failed
        exact failed
      obtain ⟨n, receiver, owned, spent⟩ := ih (cursor.after stage.1 stage.2) next
      exact ⟨⟨n.val + 1, by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using n.isLt⟩,
        receiver, owned, spent⟩
    · have spent : ownedReady cursor (EventStep.seed cursor).frame.inbox = false := Bool.eq_false_iff.mpr ready
      unfold ownedReady at spent
      split at spent
      · contradiction
      · rename_i receiver owned
        exact ⟨⟨0, by simp⟩, receiver, owned, spent⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventMemorySource
