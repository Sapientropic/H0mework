import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Runtime

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (views : List (View (code := code))) (template : Template (code := code))
  (worker : Fin code.sites)

def waiting (site : Fin code.sites) : LocalMove code site := ⟨none,List.mem_cons_self⟩

def choose (site : Fin code.sites) (moves : List (LocalMove code site)) : LocalMove code site :=
  moves.headD (waiting site)

def reads (site : Fin code.sites) : List (LocalMove code site) :=
  ((ownMoves code site).attach.filter fun move => match move.val with
    | some event => match event.val with
      | .send sender recipient => decide (code.siteParty sender = template.creditor ∧ recipient = worker)
      | _ => false
    | none => false)

def activations (site : Fin code.sites) : List (LocalMove code site) :=
  ((ownMoves code site).attach.filter fun move => match move.val with
    | some event => match event.val with | .activate _ => true | _ => false
    | none => false)

def event (site : Fin code.sites) (signal : Fin code.signals) : LocalMove code site :=
  match generate views template site signal with
  | .absent _ => waiting site
  | .ready _ _ _ _ _ => if site = worker then choose site (activations site) else waiting site
  | .ambiguous _ _ _ _ _ => choose site (reads template worker site)

def eventTable : EventTable code := fun key _ => event views template worker key.1 key.2

def supported (key : code.Key) : Prop :=
  policy views template worker key (code.key_mem key) ∈ words code.actions code.actionLimit

instance (key : code.Key) : Decidable (supported views template worker key) := by
  unfold supported;infer_instance

inductive Compiled where
  | ready (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
      (work : rule.work.val = policy views template worker)
      (events : rule.events = eventTable views template worker)
  | unsupported (key : code.Key) (original : key ∈ code.keys)
      (outside : ¬ supported views template worker key)

def compile : Compiled views template worker :=
  match inspect (supported views template worker) code.keys with
  | .accepted all => .ready
      ⟨⟨policy views template worker,code.every_local_policy_is_enumerated _ all⟩,
        eventTable views template worker⟩ rfl rfl
  | .rejected key original outside => .unsupported key original outside

theorem conflicting_local_records_generate_a_registered_own_event_or_wait
    (site : Fin code.sites) (signal : Fin code.signals)
    (attempt : Choice code)
    (actual : (event views template worker site signal).val = some attempt) :
    attempt ∈ code.eventAlphabet.attach ∧
      (match attempt.val with | .send sender _ => sender = site | .activate actor => actor = site | _ => False) := by
  have generated := (event views template worker site signal).property
  change (event views template worker site signal).val ∈ ownMoves code site at generated
  rw [actual] at generated
  have nonempty := (List.mem_cons.mp generated).resolve_left (by simp)
  obtain ⟨other,present,equal⟩ := List.mem_map.mp nonempty
  have same := Option.some.inj equal
  subst other
  exact ⟨List.mem_attach _ _,by
    have admissible := (List.mem_filter.mp present).2
    cases attempt with
    | mk action original =>
      cases action <;> simp only [Bool.false_eq_true,decide_eq_true_eq] at admissible <;> exact admissible⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry
