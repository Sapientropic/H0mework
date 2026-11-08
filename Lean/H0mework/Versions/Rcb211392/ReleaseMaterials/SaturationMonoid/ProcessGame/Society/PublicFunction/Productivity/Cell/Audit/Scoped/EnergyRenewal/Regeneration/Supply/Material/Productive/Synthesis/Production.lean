import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Production
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- The original producer finances two candidate checks. Its material and financial occurrence is retained. -/
def fund (state : State) : State :=
  if 2≤state.raw.stock supplier .labor then state
  else match state.original with
    | none => state
    | some ⟨plan,package⟩ =>
      let original := package.val
      let produced := Productive.next original .normal
      ⟨produced.session.current,produced.account,produced.session.window.scope,
       state.task,state.taskId,state.completed,some ⟨plan,produced,rfl,rfl,rfl⟩,
       state.inputs++[Productive.input original .normal]⟩

def service : JointAction :=
  ⟨receiver,[],.audit (native .common),[],.use receiver [(.energy,2)] .external⟩

def code : Code where
  need := ⟨[⟨receiver,[(.energy,2)],.external⟩],by decide +kernel,5⟩
  alphabet := [service]
  budget := 1
  charge := providerCharge
  historical := by
    intro action member
    obtain rfl := List.mem_singleton.mp member
    trivial

def advance (state : State) : State := next code (fund state)
def run (initial : State) : Nat → State
  | 0 => initial
  | count+1 => advance (run initial count)

theorem funding_uses_the_original_producer (state : State)
    (low : ¬2≤state.raw.stock supplier .labor) {plan : EnergyRenewal.Plan}
    (package : {original : Finance.State plan // original.session.current=state.raw ∧
      original.account=state.account ∧ original.session.window.scope=state.scope})
    (present : state.original=some ⟨plan,package⟩) :
    (fund state).raw=Productive.Runtime.current package.val .normal ∧
    (fund state).account=Productive.Runtime.account package.val .normal := by
  unfold fund
  rw [if_neg low,present]
  exact ⟨rfl,rfl⟩

theorem funding_preserves_the_original_law_epoch (state : State) :
    (fund state).scope=state.scope := by
  unfold fund
  split
  · rfl
  · cases state.original with
    | none => rfl
    | some package => rcases package with ⟨plan,package⟩;exact package.property.2.2

theorem funding_never_renews_or_completes_the_pending_task (state : State) :
    (fund state).task=state.task ∧ (fund state).taskId=state.taskId ∧
    (fund state).completed=state.completed := by
  unfold fund
  split
  · exact ⟨rfl,rfl,rfl⟩
  · cases state.original with
    | none => exact ⟨rfl,rfl,rfl⟩
    | some package => rcases package with ⟨plan,package⟩;exact ⟨rfl,rfl,rfl⟩

theorem original_claim_identity_survives_funding (state : State) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (fund state).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  unfold fund
  split
  · exact List.prefix_rfl
  · cases present : state.original with
    | none => exact List.prefix_rfl
    | some package =>
      rcases package with ⟨plan,package⟩
      change _ <+: (Productive.next package.val .normal).account.current.slots.map _
      have source := Productive.original_financial_admissions_keep_their_identity package.val .normal
      have same := congrArg (fun account : Finance.Account =>
        account.current.slots.map (Financial.Family.slotClaim Finance.sources)) package.property.2.1
      rw [same] at source
      exact source

theorem every_original_claim_survives_both_paid_occurrences (state : State) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (advance state).account.current.slots.map (Financial.Family.slotClaim Finance.sources) :=
  (original_claim_identity_survives_funding state).trans (every_original_financial_admission_survives code _)

theorem every_finite_production_prefix_keeps_original_claim_identity (initial : State) (count : Nat) :
    initial.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (run initial count).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ n ih => exact ih.trans (every_original_claim_survives_both_paid_occurrences _)

theorem every_original_source_successor_retains_its_full_package {plan : EnergyRenewal.Plan}
    (original : Finance.State plan) (count : Nat) :
    (run (start code original) count).original.isSome=true := by
  have funding (state : State) (presentPackage : state.original.isSome=true) :
      (fund state).original.isSome=true := by
    by_cases enough : 2≤state.raw.stock supplier .labor
    · have same : fund state=state := by unfold fund;rw [if_pos enough]
      exact (congrArg (fun s : State => s.original.isSome) same).trans presentPackage
    · cases present : state.original with
      | none => simp only [present,Option.isSome_none] at presentPackage;contradiction
      | some package =>
        rcases package with ⟨plan,package⟩
        let produced := Productive.next package.val .normal
        have same : fund state=⟨produced.session.current,produced.account,produced.session.window.scope,
            state.task,state.taskId,state.completed,some ⟨plan,produced,rfl,rfl,rfl⟩,
            state.inputs++[Productive.input package.val .normal]⟩ := by
          unfold fund
          rw [if_neg enough,present]
        exact (congrArg (fun s : State => s.original.isSome) same).trans rfl
  induction count with
  | zero => rfl
  | succ n ih =>
    change (continueOriginal code (fund (run (start code original) n))).isSome=true
    simpa only [continueOriginal,Option.isSome_map] using funding _ ih

theorem each_next_cut_uses_its_own_actual_service_after (state : State) :
    (advance state).raw=(Runtime.execution code (fund state)).after := rfl

theorem new_service_is_paid_after_real_production (state : State)
    (task : state.task.slots=code.need.slots)
    (paid : (Runtime.scan code (fund state)).succeeded=true) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law (fund state).scope)
      (Runtime.execution code (fund state)).before (Runtime.execution code (fund state)).submitted
      receiver [(.energy,2)] .external :=
  actual_service_is_paid code (fund state) paid ⟨receiver,[(.energy,2)],.external⟩ (by
    rw [(funding_never_renews_or_completes_the_pending_task state).1,task]
    exact List.mem_cons_self)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Production
