import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Plan where
  queries : Nat → Query
  larger : Bool
  births : Governance.Births
  replies : Governance.Replies
  cut : Nat
  candidate : Party

def Quiet (before : AuditCurrent) : Prop :=
  before.technology.holder = none ∧ before.technology.offered = none
instance (before : AuditCurrent) : Decidable (Quiet before) := by unfold Quiet; infer_instance

def Eligible (plan : Plan) : Prop :=
  0 < plan.cut ∧ plan.candidate ∈ Delegation.members auditTask ∧ plan.candidate ≠ 0
instance (plan : Plan) : Decidable (Eligible plan) := by unfold Eligible; infer_instance

def transfer (recipient : Party) (quantity : ℚ) : Action :=
  ⟨3,[],native .common,[],.transfer 3 recipient [(.energy,quantity)]⟩
def applicationFee : Action := ⟨0,[],native .common,[],.use 0 [(.energy,1)] .external⟩

def attempt (law : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (before : AuditCurrent) : List (AuditCurrent → Action) → List Action
  | [] => []
  | stage :: rest =>
    let action := stage before
    if law.Valid before action then action :: attempt law (law.step before action) rest else [action]

/-- These are the original supplier's goods, not a conversion of the exhausted labor balance. -/
def supplyStages (plan : Plan) : List (AuditCurrent → Action) :=
  [fun _ => transfer 0 3,fun _ => transfer plan.candidate 3,fun _ => applicationFee]

def supplyWord (plan : Plan) (before : AuditCurrent) : List Action :=
  if Eligible plan ∧ Quiet before then attempt auditLaw before (supplyStages plan) else []

def emit (plan : Plan) (before : AuditCurrent) : List Action :=
  if before.round - initial.round = plan.cut then supplyWord plan before
  else Governance.emit plan.queries plan.larger plan.births plan.replies before

/-- The supply occurrence retains the original initial World and the entire governance prefix. -/
def input (plan : Plan) : ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { Governance.input plan.queries plan.larger plan.births plan.replies with emission? := some (emit plan) }

def current (plan : Plan) : Nat → AuditCurrent :=
  Nat.rec initial (fun n before => auditLaw.next before (if n = 0 then [] else emit plan before))

theorem current_succ (plan : Plan) (n : Nat) : current plan (n+1) =
    auditLaw.next (current plan n) (if n = 0 then [] else emit plan (current plan n)) := rfl
attribute [irreducible] current

theorem current_is_own_root_current (plan : Plan) (n : Nat) :
    ProgrammeSource.rawCurrent (input plan) (ProgrammeHistory.visitAt (input plan) n).current = current plan n := by
  induction n with
  | zero => unfold current; rfl
  | succ n ih =>
    change ProgrammeSource.rawCurrent (input plan)
      (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current) = _
    rw [ProgrammeSource.actual_raw_next,ih,current_succ]
    cases n with
    | zero => rfl
    | succ n =>
      congr 1
      simp only [Nat.succ_ne_zero,if_false]
      rw [← ih]
      change ProgrammeSource.rawEvent (input plan)
        (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current) =
        emit plan (ProgrammeSource.rawCurrent (input plan)
          (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current))
      generalize (ProgrammeHistory.visitAt (input plan) n).current = prior
      cases prior <;> rfl

theorem governance_round (plan : Plan) (n : Nat) :
    (Governance.current plan.queries plan.larger plan.births plan.replies n).round = initial.round+n := by
  induction n with
  | zero => unfold Governance.current; rfl
  | succ n ih => rw [Governance.current_succ]; change _ + 1 = _; rw [ih]; omega

theorem original_prefix (plan : Plan) (n : Nat) (earlier : n ≤ plan.cut) :
    current plan n = Governance.current plan.queries plan.larger plan.births plan.replies n := by
  induction n with
  | zero => unfold current Governance.current; rfl
  | succ n ih =>
    rw [current_succ,Governance.current_succ,ih (by omega)]
    congr 1
    split
    · rfl
    · unfold emit
      rw [governance_round]
      simp only [Nat.add_sub_cancel_left,if_neg (by omega : ¬ n = plan.cut)]

def before (plan : Plan) := current plan plan.cut
def actions (plan : Plan) := supplyWord plan (before plan)
def after (plan : Plan) := current plan (plan.cut+1)

theorem before_is_the_original_governance_cut (plan : Plan) :
    before plan = Governance.Runtime.beforeAt plan.queries plan.larger plan.births plan.replies plan.cut := by
  unfold before Governance.Runtime.beforeAt
  rw [Governance.current_is_own_root_current,original_prefix plan plan.cut (by omega)]

theorem inherited_words (plan : Plan) (n : Nat) (earlier : n < plan.cut) :
    emit plan (current plan n) =
      Governance.emit plan.queries plan.larger plan.births plan.replies
        (Governance.current plan.queries plan.larger plan.births plan.replies n) := by
  rw [original_prefix plan n (by omega)]
  unfold emit
  rw [governance_round]
  simp only [Nat.add_sub_cancel_left,if_neg (by omega : ¬ n = plan.cut)]

theorem inherited_raw_items (plan : Plan) (n : Nat) (earlier : n < plan.cut) :
    auditLaw.rawItems (current plan n) (if n = 0 then [] else emit plan (current plan n)) =
      auditLaw.rawItems (Governance.current plan.queries plan.larger plan.births plan.replies n)
        (if n = 0 then [] else Governance.emit plan.queries plan.larger plan.births plan.replies
          (Governance.current plan.queries plan.larger plan.births plan.replies n)) := by
  rw [inherited_words plan n earlier,original_prefix plan n (by omega)]

theorem supply_is_the_roots_actual_word (plan : Plan) (positive : 0 < plan.cut) :
    ProgrammeSource.rawEvent (input plan) (ProgrammeHistory.visitAt (input plan) plan.cut).current = actions plan := by
  cases cut : plan.cut with
  | zero => omega
  | succ n =>
    change ProgrammeSource.rawEvent (input plan)
      (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current) = _
    have word : ProgrammeSource.rawEvent (input plan)
        (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current) =
        emit plan (ProgrammeSource.rawCurrent (input plan)
          (ProgrammeSource.next (input plan) (ProgrammeHistory.visitAt (input plan) n).current)) := by
      generalize (ProgrammeHistory.visitAt (input plan) n).current = prior
      cases prior <;> rfl
    rw [word]
    change emit plan (ProgrammeSource.rawCurrent (input plan) (ProgrammeHistory.visitAt (input plan) (n+1)).current) = _
    rw [current_is_own_root_current,← cut]
    unfold actions before emit
    rw [original_prefix plan plan.cut (by omega),governance_round]
    simp only [Nat.add_sub_cancel_left,ite_true]

theorem actual_supply_next (plan : Plan) (positive : 0 < plan.cut) :
    after plan = auditLaw.next (before plan) (actions plan) := by
  unfold after
  rw [current_succ]
  simp only [if_neg (by omega : ¬ plan.cut = 0)]
  unfold emit
  rw [original_prefix plan plan.cut (by omega),governance_round]
  simp only [Nat.add_sub_cancel_left,ite_true]
  unfold actions before
  rw [original_prefix plan plan.cut (by omega)]

def Paid (plan : Plan) : Prop :=
  (actions plan).length = 3 ∧ ∀ item ∈ auditLaw.rawItems (before plan) (actions plan),
    auditLaw.Valid item.before item.request
instance (plan : Plan) : Decidable (Paid plan) := by unfold Paid; infer_instance

structure Ready (plan : Plan) : Type where
  private mk ::
  eligible : Eligible plan
  quiet : Quiet (before plan)
  paid : Paid plan

def choose (plan : Plan) : Option (Ready plan) :=
  if eligible : Eligible plan then
    if quiet : Quiet (before plan) then
      if paid : Paid plan then some ⟨eligible,quiet,paid⟩ else none
    else none
  else none

inductive Blocked (plan : Plan) : Prop where
  | ineligible (refused : ¬ Eligible plan)
  | active (retained : ¬ Quiet (before plan))
  | unpaid (refused : ¬ Paid plan)

theorem refusal_has_an_actual_reason (plan : Plan) (absent : choose plan = none) : Blocked plan := by
  unfold choose at absent
  split at absent
  · split at absent
    · split at absent
      · cases absent
      · exact .unpaid (by assumption)
    · exact .active (by assumption)
  · exact .ineligible (by assumption)

def energySlots : List (ServiceSlot Party Good) :=
  auditTask.slots.map fun slot => ⟨slot.bearer,[(.energy,1)],slot.purpose⟩

def Ready.task {plan : Plan} (_ready : Ready plan) : PublicTaskSpec Party Good :=
  ⟨energySlots,(after plan).clock+1,(after plan).clock+1+energySlots.length,by decide +kernel⟩
def Ready.scope {plan : Plan} (ready : Ready plan) : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort) :=
  ⟨ready.task,native .machine,native .revision,by decide,[(.energy,1)]⟩

theorem task_homology : energySlots.map (fun slot => (slot.bearer,slot.purpose)) =
    auditTask.slots.map (fun slot => (slot.bearer,slot.purpose)) := by
  simp [energySlots,List.map_map]

/-- Only the new query contract uses energy; the old law and old deadline are unchanged. -/
def energyBase : RawLaw Party Good AuditPort Technology Unit :=
  { baseLaw with policy := .opaque (fun current request => Cell.law.operationAllowed current (erasePort request) &&
      decide (request.purpose.query.isSome → (if request.signer = 0 then 2 else 1) ≤ current.stock 0 .energy)) }
def Ready.law {plan : Plan} (ready : Ready plan) := Mandate.law energyBase ready.scope
def accessRequest (actor : Party) (query : Query) : Action :=
  ⟨actor,[],⟨.common,some query⟩,[native .machine],.use actor [(.energy,1)] .external⟩
def deliveryFee : Action := ⟨0,[],native .common,[],.use 0 [(.energy,1)] .external⟩

def Ready.readWord {plan : Plan} (ready : Ready plan) (before : AuditCurrent) (query : Query) : List Action :=
  attempt ready.law before [fun _ => accessRequest plan.candidate query,fun _ => deliveryFee]

def Ready.epochWord {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (before : AuditCurrent) : List Action :=
  let ordinal := before.round - (after plan).round
  if ordinal = 1 then
    attempt ready.law before
      [fun current => Mandate.request ready.scope current 0 (.propose plan.candidate),
       fun current => Mandate.request ready.scope current plan.candidate .accept,
       fun _ => accessRequest plan.candidate (queries ordinal),fun _ => deliveryFee]
  else ready.readWord before (queries ordinal)

def Ready.epochInput {plan : Plan} (ready : Ready plan) (queries : Nat → Query) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { law := ready.law, initial := after plan, instructions := [], emission? := some (ready.epochWord queries) }

def Ready.epochCurrent {plan : Plan} (ready : Ready plan) (queries : Nat → Query) : Nat → AuditCurrent :=
  Nat.rec (after plan) (fun n before => ready.law.next before (if n = 0 then [] else ready.epochWord queries before))

theorem Ready.epoch_succ {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (n : Nat) :
    ready.epochCurrent queries (n+1) = ready.law.next (ready.epochCurrent queries n)
      (if n = 0 then [] else ready.epochWord queries (ready.epochCurrent queries n)) := rfl
attribute [irreducible] Ready.epochCurrent

theorem Ready.epoch_has_exact_actual_initial {plan : Plan} (ready : Ready plan) (queries : Nat → Query) :
    (ready.epochInput queries).initial = auditLaw.next (before plan) (actions plan) :=
  actual_supply_next plan ready.eligible.1

theorem Ready.epoch_is_own_root_current {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (n : Nat) :
    ProgrammeSource.rawCurrent (ready.epochInput queries)
      (ProgrammeHistory.visitAt (ready.epochInput queries) n).current = ready.epochCurrent queries n := by
  induction n with
  | zero => unfold Ready.epochCurrent; rfl
  | succ n ih =>
    change ProgrammeSource.rawCurrent (ready.epochInput queries)
      (ProgrammeSource.next (ready.epochInput queries) (ProgrammeHistory.visitAt (ready.epochInput queries) n).current) = _
    rw [ProgrammeSource.actual_raw_next,ih,ready.epoch_succ]
    cases n with
    | zero => rfl
    | succ n =>
      congr 1
      simp only [Nat.succ_ne_zero,if_false]
      rw [← ih]
      change ProgrammeSource.rawEvent (ready.epochInput queries)
        (ProgrammeSource.next (ready.epochInput queries) (ProgrammeHistory.visitAt (ready.epochInput queries) n).current) =
        ready.epochWord queries (ProgrammeSource.rawCurrent (ready.epochInput queries)
          (ProgrammeSource.next (ready.epochInput queries) (ProgrammeHistory.visitAt (ready.epochInput queries) n).current))
      generalize (ProgrammeHistory.visitAt (ready.epochInput queries) n).current = prior
      cases prior <;> rfl

private theorem silent_execute (law : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (before : AuditCurrent) (index : Nat) (word : List Action) (silent : ∀ action ∈ word,Silent action) :
    (law.execute before index word).final.claims = before.claims := by
  induction word generalizing before index with
  | nil => rfl
  | cons head tail ih =>
    change (law.execute (law.step before head) (index+1) tail).final.claims = _
    rw [ih _ _ (fun action member => silent action (List.mem_cons_of_mem _ member))]
    unfold RawLaw.step
    split
    · change RawLaw.nextClaims before head = before.claims
      have kind := silent head List.mem_cons_self
      rcases head with ⟨signer,consents,purpose,gates,operation⟩
      cases operation <;> simp_all [Silent,RawLaw.nextClaims]
    · rfl

theorem silent_claims (law : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (before : AuditCurrent) (word : List Action) (silent : ∀ action ∈ word,Silent action) :
    (law.next before word).claims = before.claims := silent_execute law before 0 word silent

theorem attempt_silent (law : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (before : AuditCurrent) (stages : List (AuditCurrent → Action))
    (silent : ∀ stage ∈ stages,∀ current,Silent (stage current)) :
    ∀ action ∈ attempt law before stages,Silent action := by
  induction stages generalizing before with
  | nil => simp [attempt]
  | cons head tail ih =>
    unfold attempt
    dsimp only
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | member
      · exact silent head List.mem_cons_self before
      · exact ih _ (fun stage member => silent stage (List.mem_cons_of_mem _ member)) action member
    · intro action member
      exact List.mem_singleton.mp member ▸ silent head List.mem_cons_self before

theorem supply_preserves_claims (plan : Plan) (positive : 0 < plan.cut) :
    (after plan).claims = (before plan).claims := by
  rw [actual_supply_next plan positive]
  apply silent_claims
  unfold actions supplyWord
  split
  · apply attempt_silent
    simp only [supplyStages,List.mem_cons,List.not_mem_nil,or_false]
    intro stage member current
    rcases member with rfl | rfl | rfl <;> trivial
  · simp

theorem Ready.epoch_preserves_claims {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (n : Nat) :
    (ready.epochCurrent queries n).claims = (before plan).claims := by
  induction n with
  | zero => unfold Ready.epochCurrent; exact supply_preserves_claims plan ready.eligible.1
  | succ n ih =>
    rw [ready.epoch_succ]
    have preserved : (ready.law.next (ready.epochCurrent queries n)
        (if n = 0 then [] else ready.epochWord queries (ready.epochCurrent queries n))).claims =
        (ready.epochCurrent queries n).claims := by
      apply silent_claims
      split
      · simp
      · unfold Ready.epochWord
        dsimp only
        split
        · apply attempt_silent
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          intro stage member current
          rcases member with rfl | rfl | rfl | rfl <;> trivial
        · apply attempt_silent
          simp only [List.mem_cons,List.not_mem_nil,or_false]
          intro stage member current
          rcases member with rfl | rfl <;> trivial
    exact preserved.trans ih

theorem Ready.original_finance_matrix {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (n : Nat) :
    Financial.BalanceConservation.ledgerClaims Cell.source.input
      (Governance.Runtime.result plan.queries plan.larger plan.births plan.replies plan.cut).prior.oldFinance.current =
        (ready.epochCurrent queries n).claims := by
  rw [ready.epoch_preserves_claims,before_is_the_original_governance_cut]
  exact (Governance.Runtime.result plan.queries plan.larger plan.births plan.replies plan.cut).financeMatrix

theorem Ready.every_stock_flow_is_accounted {plan : Plan} (ready : Ready plan) (before : AuditCurrent)
    (word : List Action) (actor : Party) (good : Good) :
    (ready.law.next before word).stock actor good + ready.law.totalDebit (ready.law.rawItems before word) actor good =
      before.stock actor good + ready.law.totalCredit (ready.law.rawItems before word) actor good :=
  ready.law.actual_next_material_balance before word actor good

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal
