import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Feedback
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source

/-! Two actual financed histories end with the same received signal; earlier
paid information drives different real work and native repayment. Controls
cover unpaid reads, repeated receipts and refusal after memory exhaustion. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Reaction Reaction.Feedback

abbrev task : PublicTaskSpec Bool Unit :=
  ⟨[⟨false, [((), 1)], .necessity⟩], 0, 20, by decide +kernel⟩
abbrev baseLaw := {Mandate.Source.base with mandatoryMaintenance := fun _ _ => []}
abbrev scope : Mandate.Scope (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port) :=
  ⟨task, .service, .challenge, by decide +kernel, [((), 1)]⟩
abbrev law := Mandate.law baseLaw scope
abbrev initial : Mandate.Source.Current :=
  {Mandate.Source.initial with stock := fun _ _ => 10, claims := fun _ _ _ => 0}
def proposal := Mandate.request scope initial false (.propose true)
def acceptance := Mandate.request scope (law.step initial proposal) true .accept
def issue : Mandate.Source.Action := ⟨false, [], .resource, [], .issue () false true 1⟩
def tick : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 0)] .external⟩
def fee : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 1)] .contribution⟩
def repay : Mandate.Source.Action := ⟨false, [], .resource, [], .settle () false true 1⟩
abbrev serve := Mandate.Source.necessity
def originalWord (financed : Bool) := [proposal, acceptance, if financed then issue else tick]

abbrev base : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  law := law
  initial := initial
  task := task
  actions := [repay, serve]
  actionLimit := 2
  sites := 2
  signals := 2
  initialSignal := 0
  siteParty := fun site => if site = 0 then false else true
  readLocal := fun _ snapshot => if snapshot.clock < 4 ∧ 0 < snapshot.liabilities () true then 1 else 0
  sendCost := fun _ _ => [fee]
  historyAlphabet := [originalWord false, originalWord true]
  historyLimit := 1
  eventAlphabet := [.send 0 1, .deliver 0, .deliver 1, .activate 1]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro p; cases p <;> simp
  goods_cover := by intro g; cases g; simp
  instruments_cover := by intro i; cases i; simp

abbrev code := lift base 3

def programme (_site : Fin base.sites) (history : List (Notice base)) :=
  if LocalNotice.received 0 1 ∈ history then [repay, serve] else [serve]

def policy : code.Policy := tabulate base 3 programme

theorem policy_is_generated : policy ∈ code.policies := by
  apply every_supported_history_programme_is_actually_tabulated
  intro site history _
  simp only [programme]
  split <;> exact (mem_words_iff _ _ _).mpr (by simp)

def eventAt : Nat → Move code
  | 0 => some ⟨.send 0 1, by simp [code, base]⟩
  | 1 => some ⟨.deliver 0, by simp [code, base]⟩
  | 2 => some ⟨.send 0 1, by simp [code, base]⟩
  | 3 => some ⟨.deliver 1, by simp [code, base]⟩
  | 4 => some ⟨.activate 1, by simp [code, base]⟩
  | _ => none

def opponent : Opponent code := fun _ past _ => eventAt past.length

abbrev input : Input code := ⟨opponent, 5⟩

abbrev source (financed : Bool) : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code
  reference := policy
  reference_generated := policy_is_generated
  history := [originalWord financed]
  original := by
    apply List.mem_map.mpr
    refine ⟨[originalWord financed], List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply (mem_sequences_iff _ _ _).mpr
      cases financed <;> simp
    · cases financed <;> decide +kernel
  opponent := fun _ _ _ => none
  side := .original
  feedback? := some input

abbrev bound (financed : Bool) : Native.Authority.Bound (Party := Bool) (Good := Unit)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) :=
  ⟨baseLaw, scope, source financed, rfl, rfl⟩

abbrev state (financed : Bool) (index : Nat) := (source financed).feedbackState input index

abbrev receiverHistory (financed : Bool) : List (Notice base) :=
  [.received 0 (if financed then 1 else 0), .received 0 0]

def unaffordable : Mandate.Source.Action := ⟨false, [], .resource, [], .use false [((), 100)] .contribution⟩
abbrev deniedBase := {base with sendCost := fun _ _ => [unaffordable]}
abbrev deniedCode := lift deniedBase 3
def deniedOpponent : Opponent deniedCode := fun _ past _ => eventAt past.length
abbrev deniedInput : Input deniedCode := ⟨deniedOpponent, 5⟩
abbrev deniedSource : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {(source true) with
    code := deniedCode
    reference := policy
    reference_generated := policy_is_generated
    original := by decide +kernel
    feedback? := some deniedInput
    opponent := fun _ _ _ => none}

abbrev duplicateState := Reaction.Feedback.advance code (some policy)
  ⟨fun _ _ _ => eventAt 3, 1⟩ {(state true 5) with remaining := 1}

local instance noticeEq : DecidableEq (Notice base) := inferInstance

def checks : List (String × Bool) :=
  [ ("different_early_packets_are_actual_local_reads", decide
      (((state true 4).frame.sent[0]?).map (fun packet => signal base 3 packet.signal) = some 1 ∧
       ((state false 4).frame.sent[0]?).map (fun packet => signal base 3 packet.signal) = some 0)),
    ("last_received_signals_are_equal", decide
      (((state true 4).frame.sent[1]?).map (fun packet => signal base 3 packet.signal) = some 0 ∧
       ((state false 4).frame.sent[1]?).map (fun packet => signal base 3 packet.signal) = some 0)),
    ("both_local_histories_retain_the_earlier_receipt", decide
      (decode base 3 ((state true 4).frame.inbox 1) = some (receiverHistory true) ∧
       decode base 3 ((state false 4).frame.inbox 1) = some (receiverHistory false))),
    ("the_same_conditional_program_learns_different_actual_work", decide
      (((source true).actualExecution 6).submitted = [repay, serve]) && decide
      (((source false).actualExecution 6).submitted = [serve])),
    ("both_reads_are_paid_on_the_original_source", decide
      (((source true).actualExecution 2).submitted = [fee]) && decide
      (((source true).actualExecution 4).submitted = [fee])),
    ("actual_principal_is_repaid_and_native_archive_retained", decide
      (Financial.outstanding (source true).input (Native.generate (source true) 5).finance.current = 1 ∧
       Financial.outstanding (source true).input (Native.generate (source true) 6).finance.current = 0 ∧
       (Native.generate (source true) 6).finance.current.slots.length = 1)),
    ("learned_work_actually_settles_the_original_native_service", decide
      ((((Native.generate (source true) 6).services ⟨0, by decide +kernel⟩).state.slots.map
        (fun slot => match slot with | .live _ => false | .terminal _ => true)) = [true])),
    ("the_actual_attempt_is_part_of_future_local_memory", decide
      (decode base 3 ((state true 5).frame.inbox 1) = some (receiverHistory true ++ [.attempted [repay, serve]]))),
    ("the_same_planner_is_used_before_and_after_learning", decide
      ((state true 5).frame.localLegal = true ∧ (state false 5).frame.localLegal = true)),
    ("capacity_exhaustion_blocks_further_nonempty_work", decide
      (code.action policy 1 (overflow base 3) = [])),
    ("unpaid_send_cannot_create_a_packet_or_local_knowledge", decide
      (((deniedSource.feedbackState deniedInput 1).frame.sent = []) ∧
       decode base 3 ((deniedSource.feedbackState deniedInput 1).frame.inbox 0) = some [] ∧
       (deniedSource.feedbackState deniedInput 1).frame.localLegal = false)),
    ("a_duplicate_receipt_is_recorded_instead_of_erasing_old_history", decide
      (decode base 3 (duplicateState.frame.inbox 1) = none ∧
       duplicateState.frame.sent.length = 2)),
    ("overflow_remains_blocked_under_a_nonempty_proposal", decide
      ((Reaction.Feedback.advance code (some policy) ⟨fun _ _ _ => eventAt 4, 1⟩
        {duplicateState with remaining := 1}).frame.localLegal = false)) ]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Regression
