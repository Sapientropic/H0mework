import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalWireConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

namespace SourceFunding

private theorem flow_feed_zero (flow : Flow Nat Good) (absent : ∀ item∈flow,item.1.2≠Good.feed) :
    flowAt flow 3 Good.feed = 0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  have outside : entry.1 ≠ (3,Good.feed) := fun equal => absent entry inside (congrArg Prod.snd equal)
  simp only [if_neg outside]

theorem safe_step_keeps_feed (current : Scoped.AuditCurrent) (action : Scoped.Action)
    (safe : EnergyRenewal.Privacy.AuditLaw.Safe action) :
    (Scoped.auditLaw.step current action).stock 3 Good.feed = current.stock 3 Good.feed := by
  have debit := EnergyRenewal.Privacy.AuditLaw.public_debit current action safe
  have credit : ∀ item∈Scoped.auditLaw.credit current action,item.1.2≠Good.feed := by
    cases operation : action.operation <;> simp only [EnergyRenewal.Privacy.AuditLaw.Safe,operation] at safe
    case transfer sender recipient goods =>
      intro entry inside
      simp only [RawLaw.credit,operation,locate,List.mem_map] at inside
      obtain ⟨item,member,rfl⟩ := inside
      exact safe item member
    case use bearer goods purpose => cases purpose <;> simp_all [RawLaw.credit]
    case revise actor target | present => simp [RawLaw.credit,operation]
  unfold RawLaw.step
  split
  · simp only [RawLaw.paidStep,flow_feed_zero _ debit,flow_feed_zero _ credit,sub_zero,add_zero]
  · rfl

theorem safe_next_keeps_feed (current : Scoped.AuditCurrent) (word : List Scoped.Action)
    (safe : ∀ action∈word,EnergyRenewal.Privacy.AuditLaw.Safe action) (index : Nat := 0) :
    (Scoped.auditLaw.execute current index word).final.stock 3 Good.feed = current.stock 3 Good.feed := by
  induction word generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    change (Scoped.auditLaw.execute (Scoped.auditLaw.step current action) (index+1) rest).final.stock 3 Good.feed = _
    rw [ih _ (fun action inside => safe action (List.mem_cons_of_mem _ inside)) (index+1),
      safe_step_keeps_feed current action (safe action (by simp))]

theorem births_keep_current (current : Scoped.AuditCurrent) (births : Scoped.Governance.Births)
    (cut index : Nat) :
    (Scoped.auditLaw.execute current index (Scoped.Governance.bornWord births cut)).final = current := by
  have ignore (items : List Scoped.Action) (onlyBirths : ∀ action∈items,∃ key,action=Scoped.Governance.birth key)
      (current : Scoped.AuditCurrent) (index : Nat) :
      (Scoped.auditLaw.execute current index items).final = current := by
    induction items generalizing current index with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨key,rfl⟩ := onlyBirths head (by simp)
      change (Scoped.auditLaw.execute (Scoped.auditLaw.step current (Scoped.Governance.birth key)) (index+1) tail).final = _
      rw [Scoped.Governance.birth_does_not_grant_authority]
      exact ih (fun a h => onlyBirths a (List.mem_cons_of_mem _ h)) current (index+1)
  exact ignore _ (by intro action member;obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member;exact ⟨pair.2,rfl⟩) current index

theorem private_use_debits_at_most_two (current : Scoped.AuditCurrent) (larger : Bool) :
    current.stock 3 Good.feed - 2 ≤ (Scoped.auditLaw.step current (Scoped.privateUse larger)).stock 3 Good.feed ∧
    (Scoped.auditLaw.step current (Scoped.privateUse larger)).stock 3 Good.feed ≤ current.stock 3 Good.feed := by
  unfold RawLaw.step
  split
  · cases larger with
    | false => simp [Scoped.privateUse,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flowAt,locate,amount]; linarith
    | true => simp [Scoped.privateUse,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flowAt,locate,amount]
  · exact ⟨by linarith,le_rfl⟩

theorem original_emit_keeps_feed_outside_private_phase (queries : Nat → Query) (larger : Bool)
    (current : Scoped.AuditCurrent) (outside : current.round-Scoped.initial.round≠3) :
    (Scoped.auditLaw.next current (Scoped.emit queries larger current)).stock 3 Good.feed = current.stock 3 Good.feed := by
  unfold Scoped.emit
  dsimp only
  split
  · exact safe_next_keeps_feed current _ (by simp [Scoped.preparation,EnergyRenewal.Privacy.AuditLaw.Safe,Scoped.transferLabor])
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.authorization_safe _ _)
  · contradiction
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.readWord_safe _ _ _)
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.handoff_safe _)
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.readWord_safe _ _ _)
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.readWord_safe _ _ _)
  · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.readWord_safe _ _ _)
  · exact safe_next_keeps_feed current _ (by simp [Scoped.refill,EnergyRenewal.Privacy.AuditLaw.Safe,Scoped.transferLabor])
  · split
    · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.readWord_safe _ _ _)
    · rfl

theorem governance_emit_keeps_feed_outside_private_phase (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) (current : Scoped.AuditCurrent)
    (outside : current.round-Scoped.initial.round≠3) :
    (Scoped.auditLaw.next current (Scoped.Governance.emit queries larger births replies current)).stock 3 Good.feed =
      current.stock 3 Good.feed := by
  unfold Scoped.Governance.emit
  dsimp only
  simp only [RawLaw.next,RawLaw.execute_append,births_keep_current]
  split
  · split
    · rfl
    · exact safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.response_safe _ _ _)
  · exact original_emit_keeps_feed_outside_private_phase queries larger current outside

theorem governance_emit_debits_at_most_two (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) (current : Scoped.AuditCurrent)
    (privatePhase : current.round-Scoped.initial.round=3) :
    current.stock 3 Good.feed-2 ≤ (Scoped.auditLaw.next current (Scoped.Governance.emit queries larger births replies current)).stock 3 Good.feed ∧
    (Scoped.auditLaw.next current (Scoped.Governance.emit queries larger births replies current)).stock 3 Good.feed ≤ current.stock 3 Good.feed := by
  unfold Scoped.Governance.emit
  dsimp only
  simp only [RawLaw.next,RawLaw.execute_append,births_keep_current]
  split
  · split
    · change current.stock 3 Good.feed-2 ≤ current.stock 3 Good.feed ∧ current.stock 3 Good.feed ≤ current.stock 3 Good.feed
      exact ⟨by linarith,le_rfl⟩
    · rw [safe_next_keeps_feed current _ (EnergyRenewal.Privacy.GovernancePrivacy.response_safe _ _ _)]
      exact ⟨by linarith,le_rfl⟩
  · simpa only [Scoped.emit,privatePhase,RawLaw.execute,RawLaw.next,List.length_singleton] using private_use_debits_at_most_two current larger

theorem governance_round (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) (count : Nat) :
    (Scoped.Governance.current queries larger births replies count).round = Scoped.initial.round+count := by
  induction count with
  | zero => simp [Scoped.Governance.current]
  | succ n ih =>
    rw [Scoped.Governance.current_succ]
    change (Scoped.Governance.current queries larger births replies n).round+1 = _
    rw [ih]
    omega

theorem original_initial_feed : Scoped.initial.stock 3 Good.feed = 40 := by decide +kernel

theorem governance_zero (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) :
    Scoped.Governance.current queries larger births replies 0 = Scoped.initial := by
  unfold Scoped.Governance.current
  rfl

theorem governance_early_feed (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) (count : Nat) (early : count≤3) :
    (Scoped.Governance.current queries larger births replies count).stock 3 Good.feed = 40 := by
  induction count with
  | zero => rw [governance_zero];exact original_initial_feed
  | succ n ih =>
    rw [Scoped.Governance.current_succ]
    split
    · change (Scoped.Governance.current queries larger births replies n).stock 3 Good.feed = 40
      exact ih (by omega)
    · rw [governance_emit_keeps_feed_outside_private_phase queries larger births replies _ (by
        rw [governance_round,Nat.add_sub_cancel_left]
        omega)]
      exact ih (by omega)

theorem original_governance_generates_its_private_feed_range (queries : Nat → Query) (larger : Bool)
    (births : Scoped.Governance.Births) (replies : Scoped.Governance.Replies) (count : Nat) :
    38 ≤ (Scoped.Governance.current queries larger births replies count).stock 3 Good.feed ∧
      (Scoped.Governance.current queries larger births replies count).stock 3 Good.feed ≤ 40 := by
  induction count with
  | zero =>
    rw [governance_zero,original_initial_feed];norm_num
  | succ n ih =>
    rw [Scoped.Governance.current_succ]
    split
    · change 38 ≤ (Scoped.Governance.current queries larger births replies n).stock 3 Good.feed ∧
        (Scoped.Governance.current queries larger births replies n).stock 3 Good.feed ≤ 40
      exact ih
    · by_cases privatePhase : n=3
      · have prior := governance_early_feed queries larger births replies n (by omega)
        have bounds := governance_emit_debits_at_most_two queries larger births replies
          (Scoped.Governance.current queries larger births replies n) (by
            rw [governance_round,Nat.add_sub_cancel_left,privatePhase])
        rw [prior] at bounds
        exact ⟨by linarith [bounds.1],by linarith [bounds.2]⟩
      · rw [governance_emit_keeps_feed_outside_private_phase queries larger births replies _ (by
          rw [governance_round,Nat.add_sub_cancel_left]
          exact privatePhase)]
        exact ih

theorem original_before_generates_its_private_feed_range (plan : Plan) :
    38 ≤ (EnergyRenewal.before plan).stock 3 Good.feed ∧ (EnergyRenewal.before plan).stock 3 Good.feed ≤ 40 := by
  unfold EnergyRenewal.before
  rw [EnergyRenewal.original_prefix plan plan.cut (by omega)]
  exact original_governance_generates_its_private_feed_range plan.queries plan.larger plan.births plan.replies plan.cut

theorem epoch_keeps_its_original_private_feed {plan : Plan} (ready : EnergyRenewal.Ready plan)
    (queries : Nat → Query) (count : Nat) :
    (ready.epochCurrent queries count).stock 3 Good.feed = (EnergyRenewal.before plan).stock 3 Good.feed := by
  induction count with
  | zero =>
    unfold EnergyRenewal.Ready.epochCurrent
    rw [EnergyRenewal.actual_supply_next plan ready.eligible.1]
    exact safe_next_keeps_feed _ _ (EnergyRenewal.Privacy.supply_safe plan _)
  | succ n ih =>
    rw [ready.epoch_succ]
    trans (ready.epochCurrent queries n).stock 3 Good.feed
    · apply EnergyRenewal.Privacy.energy_private_execute ready.scope rfl
      split
      · simp
      · exact EnergyRenewal.Privacy.epoch_word_energy _ _ _
    · exact ih

def WindowBound {plan : Plan} (window : EnergyRenewal.Continuation.Window plan) : Prop :=
  38 ≤ window.initial.stock 3 Good.feed ∧ window.initial.stock 3 Good.feed ≤ 40

theorem first_window_is_backed {plan : Plan} (seed : EnergyRenewal.Runtime.EpochSeed plan)
    (queries : Nat → Query) (ordinal : Nat) : WindowBound (EnergyRenewal.Continuation.first seed queries ordinal) := by
  change 38 ≤ (seed.ready.epochCurrent queries (ordinal+1)).stock 3 Good.feed ∧
    (seed.ready.epochCurrent queries (ordinal+1)).stock 3 Good.feed ≤ 40
  rw [epoch_keeps_its_original_private_feed]
  exact original_before_generates_its_private_feed_range plan

theorem next_window_is_backed {plan : Plan} (window : EnergyRenewal.Continuation.Window plan) (backed : WindowBound window)
    (requests : List EnergyRenewal.Continuation.Request) (count : Nat) (next : EnergyRenewal.Continuation.Window plan)
    (generated : window.nextWindow requests count = some next) : WindowBound next := by
  unfold EnergyRenewal.Continuation.Window.nextWindow at generated
  split at generated
  · cases Option.some.inj generated
    change 38 ≤ (window.current requests (count+1)).stock 3 Good.feed ∧
      (window.current requests (count+1)).stock 3 Good.feed ≤ 40
    rw [EnergyRenewal.Privacy.window_keeps_own_private_feed]
    exact backed
  · contradiction

theorem phases_are_backed {plan : Plan} (window : EnergyRenewal.Continuation.Window plan) (backed : WindowBound window)
    (cut : Nat) (phases : List (List EnergyRenewal.Continuation.Request))
    (result : EnergyRenewal.Continuation.Window plan × Nat)
    (generated : EnergyRenewal.Privacy.phaseWindows window cut phases = .ok result) : WindowBound result.1 := by
  induction phases generalizing window cut with
  | nil => cases Except.ok.inj generated; exact backed
  | cons phase rest ih =>
    unfold EnergyRenewal.Privacy.phaseWindows at generated
    cases actual : window.nextWindow phase phase.length with
    | none => simp only [actual] at generated; contradiction
    | some next =>
      simp only [actual] at generated
      exact ih next (next_window_is_backed window backed phase phase.length next actual) _ generated

theorem initial_window_is_backed (larger : Bool) (input : EnergyRenewal.Privacy.SourceInput)
    (window : EnergyRenewal.Continuation.Window (input.plan larger))
    (generated : EnergyRenewal.Privacy.initialWindows larger input = some window) : WindowBound window := by
  unfold EnergyRenewal.Privacy.initialWindows at generated
  cases actual : EnergyRenewal.Runtime.nextEpoch (input.plan larger) with
  | none => simp only [actual] at generated; contradiction
  | some seed =>
    simp only [actual,Option.map_some] at generated
    cases Option.some.inj generated
    exact first_window_is_backed seed input.epochQueries input.ordinal

theorem handoff_window_is_backed {plan : Plan} (input : EnergyRenewal.Privacy.SourceInput)
    (window : EnergyRenewal.Continuation.Window plan) (backed : WindowBound window)
    (seed : EnergyRenewal.Handoff.Seed plan)
    (generated : EnergyRenewal.Privacy.Timing.handoffFromWindow input window = .ok seed) : WindowBound seed.window := by
  unfold EnergyRenewal.Privacy.Timing.handoffFromWindow at generated
  split at generated
  · contradiction
  · split at generated
    · contradiction
    · split at generated
      · contradiction
      · cases phases : EnergyRenewal.Privacy.phaseWindows window (input.cut+input.ordinal+2) input.commands.phases.dropLast with
        | error message => simp only [phases,Except.map] at generated; contradiction
        | ok result =>
          simp only [phases,Except.map] at generated
          cases Except.ok.inj generated
          exact phases_are_backed window backed _ _ result phases

theorem source_handoff_is_backed (larger : Bool) (input : EnergyRenewal.Privacy.SourceInput)
    (seed : EnergyRenewal.Handoff.Seed (input.plan larger))
    (generated : EnergyRenewal.Privacy.Timing.sourceHandoffSeed larger input = .ok seed) : WindowBound seed.window := by
  unfold EnergyRenewal.Privacy.Timing.sourceHandoffSeed at generated
  cases actual : EnergyRenewal.Privacy.initialWindows larger input with
  | none => simp only [actual] at generated; contradiction
  | some window =>
    simp only [actual] at generated
    exact handoff_window_is_backed input window (initial_window_is_backed larger input window actual) seed generated

theorem actual_source_initial_is_backed (larger : Bool) (input : EnergyRenewal.Privacy.SourceInput)
    (state : Finance.State (input.plan larger)) (generated : Supply.Privacy.Source.initial larger input = .ok state) :
    38 ≤ Supply.Privacy.ownFrame state.session.current ∧ Supply.Privacy.ownFrame state.session.current ≤ 40 := by
  unfold Supply.Privacy.Source.initial at generated
  cases actual : EnergyRenewal.Privacy.Timing.sourceHandoffSeed larger input with
  | error message => simp only [actual] at generated; contradiction
  | ok seed =>
    simp only [actual,Except.map] at generated
    cases Except.ok.inj generated
    have backed := source_handoff_is_backed larger input seed actual
    change 38 ≤ Supply.Privacy.ownFrame (Supply.start seed (input.commands.handoffs.getD [])).current ∧
      Supply.Privacy.ownFrame (Supply.start seed (input.commands.handoffs.getD [])).current ≤ 40
    simp only [Supply.start,Supply.initialMemo_exact,Supply.Privacy.ownFrame,Supply.join,Supply.receiver]
    rw [EnergyRenewal.Privacy.handoff_keeps_own_private_feed]
    exact backed

theorem original_productive_execution_is_backed (larger : Bool) (source : Lean.Json)
    (execution : Productive.Wire.Execution larger) (generated : Productive.Wire.execute larger source = .ok execution) :
    38 ≤ Supply.Privacy.ownFrame execution.state.session.current ∧ Supply.Privacy.ownFrame execution.state.session.current ≤ 40 := by
  unfold Productive.Wire.execute at generated
  cases parsed : Productive.Wire.decode source with
  | error message => simp only [parsed,bind,Except.bind] at generated; contradiction
  | ok decoded =>
    simp only [parsed,bind,Except.bind] at generated
    cases original : Supply.Privacy.Source.initial larger decoded.input with
    | error message => simp only [original] at generated; contradiction
    | ok state =>
      simp only [original] at generated
      cases Except.ok.inj generated
      rw [Productive.every_adaptive_prefix_keeps_its_own_private_frame,
        Supply.Privacy.every_adaptive_prefix_keeps_its_own_private_frame]
      exact actual_source_initial_is_backed larger decoded.input state original

theorem original_empty_arrival_history_is_backed (larger : Bool) (source : Lean.Json)
    (execution : History.Execution larger) (generated : History.restore larger source [] = .ok execution) :
    38 ≤ Supply.Privacy.ownFrame execution.state.service.session.current ∧
      Supply.Privacy.ownFrame execution.state.service.session.current ≤ 40 := by
  unfold History.restore at generated
  cases original : Productive.Wire.execute larger source with
  | error message => simp only [original,bind,Except.bind] at generated; contradiction
  | ok first =>
    simp only [original,bind,Except.bind] at generated
    cases Except.ok.inj generated
    exact original_productive_execution_is_backed larger source first original

theorem original_arrival_execution_is_backed (larger : Bool) (request : Lean.Json)
    (execution : ExternalArrival.Wire.Execution larger)
    (generated : ExternalArrival.Wire.execute larger request = .ok execution) :
    38 ≤ Supply.Privacy.ownFrame execution.state.service.session.current ∧
      Supply.Privacy.ownFrame execution.state.service.session.current ≤ 40 := by
  cases sourceRead : request.getObjVal? "source" with
  | error message => simp only [ExternalArrival.Wire.execute,sourceRead,bind,Except.bind] at generated; contradiction
  | ok source =>
    cases eventsRead : request.getObjValAs? (Array Lean.Json) "events" with
    | error message => simp only [ExternalArrival.Wire.execute,sourceRead,eventsRead,bind,Except.bind] at generated; contradiction
    | ok commands =>
      cases restored : History.restore larger source [] with
      | error message => simp only [ExternalArrival.Wire.execute,sourceRead,eventsRead,restored,bind,Except.bind] at generated; contradiction
      | ok first =>
        have frame := ArrivalWireConsumer.actual_execution_keeps_its_own_private_frame_and_original_admissions
          larger request source commands first execution sourceRead eventsRead restored generated
        rw [frame.2.1]
        exact original_empty_arrival_history_is_backed larger source first restored

end SourceFunding

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy
