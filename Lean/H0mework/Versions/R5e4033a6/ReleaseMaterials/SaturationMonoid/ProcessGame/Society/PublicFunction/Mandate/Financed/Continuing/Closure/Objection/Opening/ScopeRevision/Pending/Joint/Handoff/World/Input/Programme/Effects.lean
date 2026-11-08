import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Effects
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Runtime

/-! Every paid phase retains its selected source witness and is interpreted
in the single final history of this programme's existing root. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch}

structure PaidStage where
  private mk ::
  inventory : Inventory epoch
  intent : Intent
  payment : Input.Paid epoch intent (current epoch inventory.inputs)
  selected : Input.choose epoch intent (current epoch inventory.inputs) = some payment

def Execution.paidStages {inventory : Inventory epoch} (execution : Execution inventory) : List (PaidStage (epoch := epoch)) :=
  Execution.rec (motive := fun _ _ => List (PaidStage (epoch := epoch)))
    (fun _ _ _ => [])
    (fun saved payment selected => [⟨cut saved .revision,.revision,payment,selected⟩])
    (fun saved intent payment selected _ stages => ⟨cut saved intent,intent,payment,selected⟩ :: stages)
    execution

private theorem cut_is_a_record (inventory : Inventory epoch) (intent : Intent) :
    (⟨cut inventory intent,intent⟩ : Sigma fun _ : Inventory epoch => Intent) ∈ records inventory intent := by
  unfold records
  split <;> simp

theorem Execution.every_paid_stage_is_an_actual_record {inventory : Inventory epoch} (execution : Execution inventory) :
    ∀ stage ∈ execution.paidStages, (⟨stage.inventory,stage.intent⟩ : Sigma fun _ : Inventory epoch => Intent) ∈ execution.records := by
  induction execution
  next saved intent reason => simp [Execution.paidStages]
  next saved payment selected =>
    intro stage member
    cases List.mem_singleton.mp member
    exact cut_is_a_record saved .revision
  next saved intent payment selected next ih =>
    intro stage member
    rcases List.mem_cons.mp member with first | later
    · cases first
      exact List.mem_append_left _ (cut_is_a_record saved intent)
    · exact List.mem_append_right _ (ih stage later)

variable {inventory : Inventory epoch} (execution : Execution inventory)
  (stage : PaidStage (epoch := epoch)) (member : stage ∈ execution.paidStages)

def PaidStage.actual := OutstandingSource.History.actualExecution epoch.source
  (World.reviewed execution.finalInventory).inputs (stage.inventory.inputs.length + 1)

include member
theorem every_paid_stage_is_interpreted_with_its_selected_candidate :
    (stage.actual execution).submitted = Input.candidate epoch stage.intent (current epoch stage.inventory.inputs) stage.payment.choice ∧
    (stage.actual execution).before = current epoch stage.inventory.inputs := by
  have actual := each_record_is_interpreted_in_the_final_root inventory execution ⟨stage.inventory,stage.intent⟩
    (execution.every_paid_stage_is_an_actual_record stage member)
  exact ⟨actual.1.trans (Input.paid_word_is_the_actual_selected_candidate epoch _ _ stage.payment stage.selected),actual.2.1⟩

private theorem paid_stage_after_technology :
    (stage.actual execution).after.technology =
      ((Mandate.law base epoch.scope).execute (current epoch stage.inventory.inputs) 0
        (Input.candidate epoch stage.intent (current epoch stage.inventory.inputs) stage.payment.choice)).final.technology := by
  rw [(stage.actual execution).after_exact]
  change ((epoch.source.seed.law).execute (stage.actual execution).before 0 (stage.actual execution).submitted).final.technology = _
  have law : epoch.source.seed.law = Mandate.law base epoch.scope := epoch.bound.law_exact
  rw [law,(every_paid_stage_is_interpreted_with_its_selected_candidate execution stage member).1,
    (every_paid_stage_is_interpreted_with_its_selected_candidate execution stage member).2]

theorem actual_paid_exit_retires_its_own_holder (kind : stage.intent = .exit) :
    (current epoch stage.inventory.inputs).technology.holder = some stage.payment.choice.actor ∧
    (stage.actual execution).after.technology.holder = none ∧
    (stage.actual execution).after.technology.offered = none := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    rw [paid_stage_after_technology execution _ member]
    exact ⟨Input.paid_exit_is_the_original_holders_own_action epoch _ payment,
      (Input.paid_exit_retires_the_actual_holder epoch _ payment).2⟩

theorem actual_paid_admission_generates_holder_and_native_grant (kind : stage.intent = .admission) :
    (stage.actual execution).after.technology.holder = some stage.payment.choice.actor ∧
    (stage.actual execution).after.technology.offered = none ∧
    stage.inventory.grants.length < (Input.staged stage.inventory .admission).grants.length := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    rw [paid_stage_after_technology execution _ member]
    have holder := Input.paid_admission_generates_the_selected_holder epoch _ payment
    exact ⟨holder.1,holder.2,Input.paid_admission_adds_an_actual_native_grant saved payment selected⟩

theorem actual_paid_review_advances_and_expired_review_releases (kind : stage.intent = .revision) :
    (stage.actual execution).after.technology.version = (current epoch stage.inventory.inputs).technology.version + 1 ∧
    (stage.actual execution).after.technology.last = some .review ∧
    (epoch.scope.task.deadline < (current epoch stage.inventory.inputs).clock →
      (stage.actual execution).after.technology.holder = none ∧
      (stage.actual execution).after.technology.offered = none) := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    rw [paid_stage_after_technology execution _ member,Input.paid_review_advances_the_actual_authority]
    rw [Mandate.advance_version,Mandate.advance_last,Input.front_keeps_the_original_authority]
    refine ⟨rfl,rfl,?_⟩
    intro expired
    have paid := Input.an_expired_paid_review_removes_both_authority_claims epoch _ payment expired
    rw [Input.paid_review_advances_the_actual_authority] at paid
    exact paid

theorem actual_paid_admission_has_an_original_signed_grant (kind : stage.intent = .admission) :
    ∃ grant ∈ grantsAt base epoch.scope (stage.actual execution).before (stage.actual execution).submitted,
      grant.candidate = stage.payment.choice.actor ∧
      grant.acceptance.item.val.request.signer = stage.payment.choice.actor ∧
      grant.acceptance.after.technology.holder = some stage.payment.choice.actor := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    have actual := every_paid_stage_is_interpreted_with_its_selected_candidate execution
      (⟨saved,.admission,payment,selected⟩ : PaidStage) member
    rw [actual.1,actual.2]
    have present := Input.paid_admission_has_an_original_grant epoch _ payment
    generalize census : grantsAt base epoch.scope (current epoch saved.inputs)
      (Input.candidate epoch .admission (current epoch saved.inputs) payment.choice) = grants at present
    cases grants with
    | nil => cases present
    | cons grant rest =>
      have same := Input.every_admission_grant_has_the_selected_actor epoch _ payment.choice grant
      refine ⟨grant,?_,same,grant.candidate_actually_signed.trans same,?_⟩
      · exact List.mem_cons_self
      · rw [grant.holder_is_generated,same]

theorem actual_paid_challenge_has_its_own_native_birth (kind : stage.intent = .challenge) :
    ∃ active : Mandate.Response.Active (current epoch stage.inventory.inputs),
      Input.challengeResident stage.inventory active ∈ (Input.staged stage.inventory .challenge).objections ∧
      (stage.actual execution).submitted = [Input.signature epoch (Input.challenger stage.inventory active)] := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    have active : Mandate.Response.Active (current epoch saved.inputs) := payment.legal.1
    refine ⟨active,Input.challenge_resident_is_in_the_saved_next_inventory saved active,?_⟩
    have source := every_paid_stage_is_interpreted_with_its_selected_candidate execution
      (⟨saved,.challenge,payment,selected⟩ : PaidStage) member
    rw [source.1,← Input.paid_word_is_the_actual_selected_candidate epoch _ _ payment selected]
    exact Input.challenge_word_is_one_original_signature saved active

theorem actual_paid_challenge_uses_an_independent_member (kind : stage.intent = .challenge)
    (members : BothMembers epoch.scope) (holder : Bool)
    (held : (current epoch stage.inventory.inputs).technology.holder = some holder) :
    (stage.actual execution).submitted = [Input.signature epoch (!holder)] ∧ (!holder) ≠ holder := by
  obtain ⟨active,_,actual⟩ := actual_paid_challenge_has_its_own_native_birth execution stage member kind
  have independent := Input.the_actual_challenger_is_independent_of_the_holder stage.inventory active members holder held
  rw [independent.1] at actual
  exact ⟨actual,by simpa only [independent.1] using independent.2⟩

theorem actual_paid_exit_keeps_all_pre_exit_claims (kind : stage.intent = .exit) :
    (stage.actual execution).after.claims =
      (Input.commandBefore epoch .exit (current epoch stage.inventory.inputs) stage.payment.choice).claims := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    rw [(PaidStage.actual execution _).after_exact]
    change (epoch.source.seed.law.execute (PaidStage.actual execution _).before 0
      (PaidStage.actual execution _).submitted).final.claims = _
    have law : epoch.source.seed.law = Mandate.law base epoch.scope := epoch.bound.law_exact
    have actual := every_paid_stage_is_interpreted_with_its_selected_candidate execution (⟨saved,.exit,payment,selected⟩ : PaidStage) member
    rw [law,actual.1,actual.2]
    exact Input.paid_exit_keeps_all_pre_exit_claims epoch _ payment

theorem actual_paid_renewal_keeps_holder_and_advances_its_command (kind : stage.intent = .renewal) :
    (stage.actual execution).after.technology.holder = (current epoch stage.inventory.inputs).technology.holder ∧
    (stage.actual execution).after.technology.last = some .renew := by
  cases stage
  next saved intent payment selected =>
    dsimp only at kind
    cases kind
    rw [paid_stage_after_technology execution _ member]
    exact Input.paid_renewal_is_the_same_holders_fresh_command epoch _ payment

def PaidStage.EffectAt (stage : PaidStage (epoch := epoch)) (after : Current) (submitted : List Action) : Prop :=
  match stage.intent with
  | .admission =>
    after.technology.holder = some stage.payment.choice.actor ∧
    after.technology.offered = none ∧
    stage.inventory.grants.length < (Input.staged stage.inventory .admission).grants.length
  | .challenge =>
    ∃ active : Mandate.Response.Active (current epoch stage.inventory.inputs),
      Input.challengeResident stage.inventory active ∈ (Input.staged stage.inventory .challenge).objections ∧
      submitted = [Input.signature epoch (Input.challenger stage.inventory active)]
  | .exit =>
    (current epoch stage.inventory.inputs).technology.holder = some stage.payment.choice.actor ∧
    after.technology.holder = none ∧
    after.technology.offered = none ∧
    after.claims =
      (Input.commandBefore epoch .exit (current epoch stage.inventory.inputs) stage.payment.choice).claims
  | .revision =>
    after.technology.version = (current epoch stage.inventory.inputs).technology.version + 1 ∧
    after.technology.last = some .review ∧
    (epoch.scope.task.deadline < (current epoch stage.inventory.inputs).clock →
      after.technology.holder = none ∧
      after.technology.offered = none)
  | .renewal =>
    after.technology.holder = (current epoch stage.inventory.inputs).technology.holder ∧
    after.technology.last = some .renew

def PaidStage.Effect : Prop :=
  stage.EffectAt (stage.actual execution).after (stage.actual execution).submitted

theorem every_paid_phase_has_its_actual_native_effect : stage.Effect execution := by
  unfold PaidStage.Effect PaidStage.EffectAt
  split
  next kind => exact actual_paid_admission_generates_holder_and_native_grant execution stage member kind
  next kind => exact actual_paid_challenge_has_its_own_native_birth execution stage member kind
  next kind =>
    have exit := actual_paid_exit_retires_its_own_holder execution stage member kind
    exact ⟨exit.1,exit.2.1,exit.2.2,actual_paid_exit_keeps_all_pre_exit_claims execution stage member kind⟩
  next kind => exact actual_paid_review_advances_and_expired_review_releases execution stage member kind
  next kind => exact actual_paid_renewal_keeps_holder_and_advances_its_command execution stage member kind

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme
