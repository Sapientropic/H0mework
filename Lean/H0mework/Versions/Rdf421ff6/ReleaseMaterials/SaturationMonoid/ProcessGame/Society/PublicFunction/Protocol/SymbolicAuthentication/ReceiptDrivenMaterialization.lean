import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRun
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRuleTable

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenMaterialization
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat) (rival : Opponent model.source.code)

abbrev Stages := ReceiptDrivenRun.Stages model
structure Slot where
  rule : Rule model.source.code
  move : Move model.source.code
  pending : ReceiptDrivenRun.Mailbox model
abbrev Slots := List (Slot model)

def extend (past : Stages model) (slots : Slots model) := past ++ slots.map fun slot => (slot.rule, EventStep.fixed slot.move)

def checkStep (past : Stages model) (pending : ReceiptDrivenRun.Mailbox model) (base : Rule model.source.code)
    (slot : Slot model) :=
  let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
  LocalRuleTable.verify slot.rule (ReceiptDrivenRule.protocol base queued) &&
    decide ((InterferenceEnvelope.observe start past allowance rival).admitted = slot.move) &&
    (List.finRange model.source.code.sites).all fun site => decide
      (ReceiptDrivenRule.consume queued
        (StageTrace.material (EventHistory.execute start past) slot.rule (EventStep.fixed slot.move)) site = slot.pending site)

theorem checked_step_is_the_complete_actual_source_step
    (past : Stages model) (pending : ReceiptDrivenRun.Mailbox model) (base : Rule model.source.code) (slot : Slot model)
    (checked : checkStep model start vocabulary encoding law allowance rival past pending base slot = true) :
    let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
    ReceiptDrivenRule.protocol base queued = slot.rule ∧
      (InterferenceEnvelope.observe start past allowance rival).admitted = slot.move ∧
      ReceiptDrivenRule.consume queued
        (StageTrace.material (EventHistory.execute start past) slot.rule (EventStep.fixed slot.move)) = slot.pending := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨(LocalRuleTable.verified_table_is_the_entire_original_rule _ _ checked.1.1).symm, checked.1.2, ?_⟩
  funext site
  exact of_decide_eq_true ((List.all_eq_true.mp checked.2) site (List.mem_finRange _))

def verify : List (Rule model.source.code) → Stages model → ReceiptDrivenRun.Mailbox model → Slots model → Bool
  | [], _, _, [] => true
  | base :: tail, past, pending, slot :: rest =>
    if UnifiedResponse.fuel model start past = 0 then false
    else checkStep model start vocabulary encoding law allowance rival past pending base slot &&
      verify tail (LocalWindowRun.after model past slot.rule slot.move) slot.pending rest
  | _, _, _, _ => false

def finalPending : ReceiptDrivenRun.Mailbox model → Slots model → ReceiptDrivenRun.Mailbox model
  | pending, [] => pending
  | _, slot :: rest => finalPending slot.pending rest

-- The active executor never accepts this trace as input. This checks its complete
-- rule, source input and local queue transition, before any final Goal is tested.
theorem verified_slots_are_the_original_dynamic_executor
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : ReceiptDrivenRun.Mailbox model) (slots : Slots model)
    (checked : verify model start vocabulary encoding law allowance rival programme past pending slots = true) :
    let actual := ReceiptDrivenRun.run model start vocabulary encoding law allowance programme past pending rival
    let terminal := ReceiptDrivenRun.run model start vocabulary encoding law allowance [] (extend model past slots) (finalPending model pending slots) rival
    actual.state = terminal.state ∧ actual.status = terminal.status ∧ actual.pending = terminal.pending := by
  induction programme generalizing past pending slots with
  | nil =>
    cases slots with
    | nil => simp only [extend, finalPending, List.map_nil, List.append_nil, and_self]
    | cons => simp only [verify, Bool.false_eq_true] at checked
  | cons base tail ih =>
    cases slots with
    | nil => simp only [verify, Bool.false_eq_true] at checked
    | cons slot rest =>
      by_cases live : UnifiedResponse.fuel model start past = 0
      · simp only [verify, if_pos live, Bool.false_eq_true] at checked
      · simp only [verify, if_neg live, Bool.and_eq_true] at checked
        obtain ⟨generated, selected, consumed⟩ :=
          checked_step_is_the_complete_actual_source_step model start vocabulary encoding law allowance rival past pending base slot checked.1
        dsimp only
        simp only [ReceiptDrivenRun.run, if_neg live, generated, selected, consumed]
        have later := ih (LocalWindowRun.after model past slot.rule slot.move) slot.pending rest checked.2
        have last : finalPending model pending (slot :: rest) = finalPending model slot.pending rest := by
          rfl
        simpa only [extend, LocalWindowRun.after, List.map_cons, List.append_assoc, List.singleton_append, last, ReceiptDrivenRun.run] using later

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenMaterialization
