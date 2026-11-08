import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Observation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Source
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open EnergyRenewal.Privacy

/-- The only original private debit belongs to actor 3; every other feed coordinate remains public. -/
def FrameSafe (action : Action) : Prop := match action.operation with
  | .transfer _ _ goods => ∀ entry∈goods,entry.1≠Good.feed
  | .use actor goods .external => actor=3 ∨ ∀ entry∈goods,entry.1≠Good.feed
  | .revise _ _ | .present => True
  | _ => False

private theorem flow_absent (flow : Flow Party Good) (actor : Party)
    (absent : ∀ entry∈flow,entry.1≠(actor,Good.feed)) : flowAt flow actor .feed=0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  simp only [if_neg (absent entry inside)]

theorem frame_step (before : AuditCurrent) (action : Action) (safe : FrameSafe action)
    (actor : Party) (outside : actor≠3) : (auditLaw.step before action).stock actor .feed=before.stock actor .feed := by
  have debit : ∀ entry∈auditLaw.debit before action,entry.1≠(actor,Good.feed) := by
    cases op : action.operation <;> simp only [FrameSafe,op] at safe
    case transfer p q goods =>
      intro entry member
      simp only [RawLaw.debit,op,locate,List.mem_map] at member
      obtain ⟨item,inside,rfl⟩ := member
      intro equal
      exact safe item inside (congrArg Prod.snd equal)
    case use p goods kind =>
      cases kind <;> try contradiction
      intro entry member
      simp only [RawLaw.debit,op,locate,List.mem_map] at member
      obtain ⟨item,inside,rfl⟩ := member
      intro equal
      rcases safe with rfl | safe
      · exact outside (congrArg Prod.fst equal).symm
      · exact safe item inside (congrArg Prod.snd equal)
    case revise p target => simp [RawLaw.debit,op,auditLaw,Mandate.law,Scoped.scope,locate]
    case present => simp [RawLaw.debit,op]
  have credit : ∀ entry∈auditLaw.credit before action,entry.1≠(actor,Good.feed) := by
    cases op : action.operation <;> simp only [FrameSafe,op] at safe
    case transfer p q goods =>
      intro entry member
      simp only [RawLaw.credit,op,locate,List.mem_map] at member
      obtain ⟨item,inside,rfl⟩ := member
      intro equal
      exact safe item inside (congrArg Prod.snd equal)
    case use p goods kind | revise p target | present => simp [RawLaw.credit,op]
  unfold RawLaw.step
  split
  · simp only [RawLaw.paidStep,flow_absent _ actor debit,flow_absent _ actor credit,sub_zero,add_zero]
  · rfl

theorem frame_execute (before : AuditCurrent) (actions : List Action)
    (safe : ∀ action∈actions,FrameSafe action) (index actor : Nat) (outside : actor≠3) :
    (auditLaw.execute before index actions).final.stock actor .feed=before.stock actor .feed := by
  induction actions generalizing before index with
  | nil => rfl
  | cons action rest ih =>
    change (auditLaw.execute (auditLaw.step before action) (index+1) rest).final.stock actor .feed=_
    rw [ih _ (fun action member => safe action (List.mem_cons_of_mem _ member)) (index+1),
      frame_step _ _ (safe action (by simp)) actor outside]

theorem audit_safe_frame (action : Action) (safe : AuditLaw.Safe action) : FrameSafe action := by
  cases op : action.operation <;> simp only [AuditLaw.Safe,FrameSafe,op] at *
  all_goals try trivial
  case use p goods kind => cases kind <;> simp_all; exact Or.inr safe

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem original_emit_frame (queries : Nat → Query) (larger : Bool) (current : AuditCurrent) :
    ∀ action∈Scoped.emit queries larger current,FrameSafe action := by
  unfold Scoped.emit Scoped.preparation Scoped.refill Scoped.handoff Scoped.authorization Scoped.readWord
  dsimp only
  repeat' split
  all_goals simp [FrameSafe,Scoped.transferLabor,Scoped.command,Mandate.request,
    Scoped.privateUse,Scoped.accessRequest,Scoped.deliveryFee]

theorem governance_emit_frame (queries : Nat → Query) (larger : Bool) (births : Governance.Births)
    (replies : Governance.Replies) (current : AuditCurrent) :
    ∀ action∈Governance.emit queries larger births replies current,FrameSafe action := by
  unfold Governance.emit
  dsimp only
  intro action member
  rcases List.mem_append.mp member with old | born
  · split at old
    · split at old
      · simp at old
      · exact audit_safe_frame action (GovernancePrivacy.response_safe _ _ _ action old)
    · exact original_emit_frame _ _ _ action old
  · simp only [Governance.bornWord,List.mem_map] at born
    obtain ⟨entry,_,rfl⟩ := born
    trivial

theorem plan_emit_frame (plan : Plan) (current : AuditCurrent) :
    ∀ action∈EnergyRenewal.emit plan current,FrameSafe action := by
  unfold EnergyRenewal.emit
  split
  · intro action member
    exact audit_safe_frame action (supply_safe plan current action member)
  · exact governance_emit_frame _ _ _ _ _

theorem original_plan_keeps_all_public_fuel (plan : Plan) (n actor : Nat) (outside : actor≠3) :
    (EnergyRenewal.current plan n).stock actor .feed=Scoped.initial.stock actor .feed := by
  induction n with
  | zero => unfold EnergyRenewal.current;rfl
  | succ n ih =>
    rw [EnergyRenewal.current_succ]
    trans (EnergyRenewal.current plan n).stock actor .feed
    · apply frame_execute
      split
      · simp
      · exact plan_emit_frame _ _
      exact outside
    · exact ih

theorem original_epoch_keeps_all_public_fuel {plan : Plan} (ready : Ready plan)
    (queries : Nat → Query) (n actor : Nat) (outside : actor≠3) :
    (ready.epochCurrent queries n).stock actor .feed=Scoped.initial.stock actor .feed := by
  induction n with
  | zero =>
    unfold Ready.epochCurrent
    exact original_plan_keeps_all_public_fuel plan (plan.cut+1) actor outside
  | succ n ih =>
    rw [ready.epoch_succ]
    trans (ready.epochCurrent queries n).stock actor .feed
    · apply energy_private_execute ready.scope rfl
      split
      · simp
      · exact epoch_word_energy _ _ _
    · exact ih

def WindowFuel {plan : Plan} (window : Continuation.Window plan) : Prop :=
  ∀ actor,actor≠3 → window.initial.stock actor .feed=Scoped.initial.stock actor .feed

theorem first_fuel {plan : Plan} (seed : Runtime.EpochSeed plan) (queries : Nat → Query) (ordinal : Nat) :
    WindowFuel (Continuation.first seed queries ordinal) := by
  intro actor outside
  exact original_epoch_keeps_all_public_fuel seed.ready queries (ordinal+1) actor outside

theorem next_fuel {plan : Plan} (window : Continuation.Window plan) (fuel : WindowFuel window)
    (requests : List Continuation.Request) (n : Nat) (next : Continuation.Window plan)
    (generated : window.nextWindow requests n=some next) : WindowFuel next := by
  unfold Continuation.Window.nextWindow at generated
  split at generated
  · cases Option.some.inj generated
    intro actor outside
    exact (window_keeps_own_private_feed window requests (n+1) actor).trans (fuel actor outside)
  · contradiction

theorem phases_fuel {plan : Plan} (window : Continuation.Window plan) (fuel : WindowFuel window)
    (cut : Nat) (phases : List (List Continuation.Request)) (result : Continuation.Window plan × Nat)
    (generated : phaseWindows window cut phases=.ok result) : WindowFuel result.1 := by
  induction phases generalizing window cut with
  | nil => cases Except.ok.inj generated;exact fuel
  | cons phase rest ih =>
    unfold phaseWindows at generated
    cases actual : window.nextWindow phase phase.length with
    | none => simp only [actual] at generated;contradiction
    | some next =>
      simp only [actual] at generated
      exact ih next (next_fuel window fuel phase phase.length next actual) _ generated

/-- This invariant is generated by the original source, including every governance reply and first paid supply. -/
theorem handoff_source_fuel (larger : Bool) (input : SourceInput) (seed : Handoff.Seed (input.plan larger))
    (generated : Timing.sourceHandoffSeed larger input=.ok seed) : WindowFuel seed.window := by
  unfold Timing.sourceHandoffSeed initialWindows at generated
  cases actual : Runtime.nextEpoch (input.plan larger) with
  | none => simp only [actual,Option.map_none,Option.elim_none] at generated;contradiction
  | some origin =>
    simp only [actual,Option.map_some,Option.elim_some] at generated
    unfold Timing.handoffFromWindow at generated
    split at generated
    · contradiction
    · split at generated
      · contradiction
      · split at generated
        · contradiction
        · cases phases : phaseWindows (Continuation.first origin input.epochQueries input.ordinal)
              (input.cut+input.ordinal+2) input.commands.phases.dropLast with
          | error message => simp only [phases,Except.map_error] at generated;contradiction
          | ok result =>
            simp only [phases,Except.map_ok] at generated
            cases Except.ok.inj generated
            exact phases_fuel _ (first_fuel _ _ _) _ _ result phases

structure SessionTwin {lp rp : Plan} (left : Session lp) (right : Session rp) : Prop where
  current : Supply.Privacy.Twin left.current right.current
  scope : left.window.scope=right.window.scope
  target : left.target=right.target
  history : left.history.length=right.history.length

theorem generated_starts_are_related {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) (leftFuel : WindowFuel left.window) (rightFuel : WindowFuel right.window)
    (received : List Handoff.Request) : SessionTwin (Supply.start left received) (Supply.start right received) := by
  have currents : EnergyRenewal.Privacy.Twin
      (left.current received (left.ordinal+received.length+1))
      (right.current received (right.ordinal+received.length+1)) := by
    rw [←same.ordinal]
    exact same.current received (left.ordinal+received.length+1)
  have joint : Supply.Privacy.Twin
      (join (left.current received (left.ordinal+received.length+1)) providerInitial)
      (join (right.current received (right.ordinal+received.length+1)) providerInitial) := by
    refine ⟨?_,currents.clock,currents.round,?_,?_⟩
    · simp only [join,currents.technology,currents.clock,currents.round]
    · simp only [join,currents.claims]
    · intro actor good outside
      cases actor with
      | inr provider => rfl
      | inl actor =>
        change (left.current received (left.ordinal+received.length+1)).stock actor good=
          (right.current received (right.ordinal+received.length+1)).stock actor good
        by_cases feed : good=Good.feed
        · subst good
          have actorOutside : actor≠3 := by intro equal;apply outside;subst actor;rfl
          rw [handoff_keeps_own_private_feed,handoff_keeps_own_private_feed,
            leftFuel actor actorOutside,rightFuel actor actorOutside]
        · exact currents.stock actor good feed
  refine ⟨?_,same.window.scope,?_,rfl⟩
  · simpa only [Supply.start,initialMemo_exact] using joint
  · simp only [Supply.start,Handoff.Seed.candidates,Handoff.Seed.scope,same.window.scope,
      currents.technology]

def initial (larger : Bool) (input : SourceInput) : Except String (Finance.State (input.plan larger)) :=
  (Timing.sourceHandoffSeed larger input).map fun seed => Finance.start (Supply.start seed (input.commands.handoffs.getD []))

/-- No ready world, privacy relation, endpoint or successful supply is provided by the caller. -/
theorem original_source_generates_new_supply_initial_relation (input : SourceInput) :
    ResultRel (fun left right => SessionTwin left.session right.session ∧ left.account=right.account)
      (initial false input) (initial true input) := by
  have matched := Timing.original_source_generates_related_handoff_seeds true input
  unfold initial
  cases left : Timing.sourceHandoffSeed false input with
  | error message =>
    cases right : Timing.sourceHandoffSeed true input with
    | error other =>
      rw [left,right] at matched
      cases matched
      exact .error _
    | ok seed => rw [left,right] at matched;cases matched
  | ok seed =>
    cases right : Timing.sourceHandoffSeed true input with
    | error message => rw [left,right] at matched;cases matched
    | ok other =>
      rw [left,right] at matched
      cases matched with
      | ok same =>
        exact .ok ⟨generated_starts_are_related same (handoff_source_fuel false input seed left)
          (handoff_source_fuel true input other right) _,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Source
