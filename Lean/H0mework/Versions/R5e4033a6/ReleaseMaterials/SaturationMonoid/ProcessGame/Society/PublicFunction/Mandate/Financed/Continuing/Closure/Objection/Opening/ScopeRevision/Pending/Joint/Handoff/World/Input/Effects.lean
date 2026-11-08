import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime

/-! Actual paid candidates generate authority effects and native births.
Material preparation never changes authority; exit does not clear old claims. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable (epoch : Epoch)

private theorem execute_final_index (before : Current) (word : List Action) (first second : Nat) :
    ((Mandate.law base epoch.scope).execute before first word).final =
      ((Mandate.law base epoch.scope).execute before second word).final := by
  induction word generalizing before first second with
  | nil => rfl
  | cons action tail ih => exact ih _ _ _

def commandBefore (intent : Intent) (before : Current) (choice : Choice) :=
  ((Mandate.law base epoch.scope).execute before 0 (front epoch intent before choice)).final

private theorem command_items (intent : Intent) (before : Current) (choice : Choice) :
    (Mandate.law base epoch.scope).rawItems before (candidate epoch intent before choice) =
      ((Mandate.law base epoch.scope).execute before 0 (front epoch intent before choice)).items ++
      ((Mandate.law base epoch.scope).execute (commandBefore epoch intent before choice)
        (front epoch intent before choice).length (commands epoch intent (commandBefore epoch intent before choice) choice.actor)).items := by
  unfold RawLaw.rawItems candidate
  rw [(Mandate.law base epoch.scope).execute_append]
  simp only [Nat.zero_add, commandBefore]

private theorem command_final (intent : Intent) (before : Current) (choice : Choice) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch intent before choice)).final =
      ((Mandate.law base epoch.scope).execute (commandBefore epoch intent before choice) 0
        (commands epoch intent (commandBefore epoch intent before choice) choice.actor)).final := by
  unfold candidate
  rw [(Mandate.law base epoch.scope).execute_append]
  exact execute_final_index epoch _ _ _ _

private theorem signature_step (before : Current) (actor : Bool) :
    (Mandate.law base epoch.scope).step before (signature epoch actor) = before :=
  (Mandate.law base epoch.scope).presentation_preserves_material_and_claims before _ rfl

def exitItem (before : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(front epoch .exit before choice).length + 1, commandBefore epoch .exit before choice,
    request epoch.scope (commandBefore epoch .exit before choice) choice.actor .exit⟩

theorem exit_item_is_actual (before : Current) (choice : Choice) :
    exitItem epoch before choice ∈ (Mandate.law base epoch.scope).rawItems before (candidate epoch .exit before choice) := by
  rw [command_items]
  apply List.mem_append_right
  simp only [commands, RawLaw.execute, signature_step, exitItem, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr True.intro

theorem paid_exit_retires_the_actual_holder (before : Current) (paid : Paid epoch .exit before) :
    (commandBefore epoch .exit before paid.choice).technology.holder = some paid.choice.actor ∧
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .exit before paid.choice)).final.technology.holder = none ∧
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .exit before paid.choice)).final.technology.offered = none := by
  have valid := paid.legal.2 _ (exit_item_is_actual epoch before paid.choice)
  have owns := (Mandate.command_policy base epoch.scope _ _ .exit).mp valid.1.2
  have effect := Mandate.paid_command_effect base epoch.scope _ _ .exit valid
  dsimp only [exitItem] at owns effect
  rw [command_final]
  simp only [commands, RawLaw.execute, signature_step]
  rw [effect.1]
  exact ⟨owns, rfl, rfl⟩

def reviewItem (before : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(front epoch .revision before choice).length, commandBefore epoch .revision before choice,
    request epoch.scope (commandBefore epoch .revision before choice) choice.actor .review⟩

theorem review_item_is_actual (before : Current) (choice : Choice) :
    reviewItem epoch before choice ∈ (Mandate.law base epoch.scope).rawItems before (candidate epoch .revision before choice) := by
  rw [command_items]
  apply List.mem_append_right
  exact List.mem_cons_self

theorem paid_review_advances_the_actual_authority (before : Current) (paid : Paid epoch .revision before) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .revision before paid.choice)).final.technology =
      Mandate.advance epoch.scope (commandBefore epoch .revision before paid.choice) .review := by
  have valid := paid.legal.2 _ (review_item_is_actual epoch before paid.choice)
  rw [command_final]
  simp only [commands, RawLaw.execute, signature_step]
  exact (Mandate.paid_command_effect base epoch.scope _ _ .review valid).1

private theorem recognized_item (before : Current) (word : List Action)
    (item : {item // item ∈ (Mandate.law base epoch.scope).rawItems before word})
    (event : ActualCommand base epoch.scope before word)
    (found : recognize base epoch.scope before word item = some event) : event.item = item := by
  unfold recognize at found
  split at found
  · split at found
    · cases found
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  · cases found

def proposalItem (before : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(front epoch .admission before choice).length, commandBefore epoch .admission before choice,
    request epoch.scope (commandBefore epoch .admission before choice) (sponsor epoch) (.propose choice.actor)⟩

def acceptanceBefore (before : Current) (choice : Choice) :=
  (Mandate.law base epoch.scope).step (commandBefore epoch .admission before choice) (proposalItem epoch before choice).request

def acceptanceItem (before : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(front epoch .admission before choice).length + 1, acceptanceBefore epoch before choice,
    request epoch.scope (acceptanceBefore epoch before choice) choice.actor .accept⟩

theorem admission_pair_is_actual (before : Current) (choice : Choice) :
    proposalItem epoch before choice ∈ (Mandate.law base epoch.scope).rawItems before (candidate epoch .admission before choice) ∧
    acceptanceItem epoch before choice ∈ (Mandate.law base epoch.scope).rawItems before (candidate epoch .admission before choice) := by
  rw [command_items]
  constructor <;> apply List.mem_append_right
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

def admissionProposal (before : Current) (paid : Paid epoch .admission before) :
    ActualCommand base epoch.scope before (candidate epoch .admission before paid.choice) :=
  (recognize base epoch.scope before _ ⟨proposalItem epoch before paid.choice,(admission_pair_is_actual epoch before paid.choice).1⟩).get (by
    have accepted := paid.legal.2 _ (admission_pair_is_actual epoch before paid.choice).1
    simp_all only [recognize, proposalItem, request, Mandate.advance, Option.isSome_some, ↓reduceDIte])

def admissionAcceptance (before : Current) (paid : Paid epoch .admission before) :
    ActualCommand base epoch.scope before (candidate epoch .admission before paid.choice) :=
  (recognize base epoch.scope before _ ⟨acceptanceItem epoch before paid.choice,(admission_pair_is_actual epoch before paid.choice).2⟩).get (by
    have accepted := paid.legal.2 _ (admission_pair_is_actual epoch before paid.choice).2
    simp_all only [recognize, acceptanceItem, request, Mandate.advance, Option.isSome_some, ↓reduceDIte])

theorem admission_pair_facts (before : Current) (paid : Paid epoch .admission before) :
    (admissionProposal epoch before paid).item.val = proposalItem epoch before paid.choice ∧
    (admissionAcceptance epoch before paid).item.val = acceptanceItem epoch before paid.choice ∧
    (admissionProposal epoch before paid).command = .propose paid.choice.actor ∧
    (admissionAcceptance epoch before paid).command = .accept ∧
    admissionProposal epoch before paid ∈ commandsAt base epoch.scope before (candidate epoch .admission before paid.choice) ∧
    admissionAcceptance epoch before paid ∈ commandsAt base epoch.scope before (candidate epoch .admission before paid.choice) := by
  have firstRead : recognize base epoch.scope before _ ⟨proposalItem epoch before paid.choice,(admission_pair_is_actual epoch before paid.choice).1⟩ =
      some (admissionProposal epoch before paid) := (Option.some_get _).symm
  have secondRead : recognize base epoch.scope before _ ⟨acceptanceItem epoch before paid.choice,(admission_pair_is_actual epoch before paid.choice).2⟩ =
      some (admissionAcceptance epoch before paid) := (Option.some_get _).symm
  have first := congrArg Subtype.val (recognized_item epoch before _ _ _ firstRead)
  have second := congrArg Subtype.val (recognized_item epoch before _ _ _ secondRead)
  have firstOp := (admissionProposal epoch before paid).operation
  have secondOp := (admissionAcceptance epoch before paid).operation
  rw [first] at firstOp
  rw [second] at secondOp
  have firstMark := (admissionProposal epoch before paid).marked
  have secondMark := (admissionAcceptance epoch before paid).marked
  rw [← (Operation.revise.inj firstOp).2, Mandate.advance_last] at firstMark
  rw [← (Operation.revise.inj secondOp).2, Mandate.advance_last] at secondMark
  exact ⟨first,second,(Option.some.inj firstMark).symm,(Option.some.inj secondMark).symm,
    List.mem_filterMap.mpr ⟨_,List.mem_attach _ _,firstRead⟩,
    List.mem_filterMap.mpr ⟨_,List.mem_attach _ _,secondRead⟩⟩

theorem paid_admission_has_an_original_grant (before : Current) (paid : Paid epoch .admission before) :
    (grantsAt base epoch.scope before (candidate epoch .admission before paid.choice)).isEmpty = false := by
  have facts := admission_pair_facts epoch before paid
  have linked : (admissionProposal epoch before paid).item.val.index < (admissionAcceptance epoch before paid).item.val.index ∧
      (admissionProposal epoch before paid).after.technology = (admissionAcceptance epoch before paid).item.val.before.technology := by
    constructor
    · rw [facts.1,facts.2.1]; exact Nat.lt_succ_self _
    · rw [ActualCommand.after,facts.1,facts.2.1]; rfl
  by_contra empty
  have nil : grantsAt base epoch.scope before (candidate epoch .admission before paid.choice) = [] := by simpa using empty
  unfold grantsAt at nil
  have branch := List.flatMap_eq_nil_iff.mp nil _ facts.2.2.2.2.1
  have absent := List.filterMap_eq_nil_iff.mp branch _ facts.2.2.2.2.2
  split at absent
  · split at absent
    · cases absent
    · rename_i denied
      exact denied linked
  · simp_all

theorem paid_admission_generates_the_selected_holder (before : Current) (paid : Paid epoch .admission before) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .admission before paid.choice)).final.technology.holder = some paid.choice.actor ∧
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .admission before paid.choice)).final.technology.offered = none := by
  have first := paid.legal.2 _ (admission_pair_is_actual epoch before paid.choice).1
  have second := paid.legal.2 _ (admission_pair_is_actual epoch before paid.choice).2
  have firstEffect := Mandate.paid_command_effect base epoch.scope _ _ (.propose paid.choice.actor) first
  have secondEffect := Mandate.paid_command_effect base epoch.scope _ _ .accept second
  dsimp only [proposalItem] at firstEffect
  dsimp only [acceptanceItem] at secondEffect
  rw [command_final]
  simp only [commands, if_true, RawLaw.execute, signature_step]
  change ((Mandate.law base epoch.scope).step (acceptanceBefore epoch before paid.choice)
    (request epoch.scope (acceptanceBefore epoch before paid.choice) paid.choice.actor .accept)).technology.holder = _ ∧
    ((Mandate.law base epoch.scope).step (acceptanceBefore epoch before paid.choice)
    (request epoch.scope (acceptanceBefore epoch before paid.choice) paid.choice.actor .accept)).technology.offered = none
  rw [secondEffect.1]
  constructor
  · change (acceptanceBefore epoch before paid.choice).technology.offered = some paid.choice.actor
    rw [show (acceptanceBefore epoch before paid.choice).technology = _ from firstEffect.1]
    rfl
  · rfl

private theorem execute_clock (before : Current) (index : Nat) (word : List Action) :
    ((Mandate.law base epoch.scope).execute before index word).final.clock = before.clock := by
  induction word generalizing before index with
  | nil => rfl
  | cons action tail ih =>
    change ((Mandate.law base epoch.scope).execute ((Mandate.law base epoch.scope).step before action) (index+1) tail).final.clock = _
    rw [ih]
    unfold RawLaw.step
    split <;> rfl

theorem an_expired_paid_review_removes_both_authority_claims (before : Current) (paid : Paid epoch .revision before)
    (expired : epoch.scope.task.deadline < before.clock) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .revision before paid.choice)).final.technology.holder = none ∧
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .revision before paid.choice)).final.technology.offered = none := by
  rw [paid_review_advances_the_actual_authority]
  have clock : (commandBefore epoch .revision before paid.choice).clock = before.clock := execute_clock epoch _ _ _
  simp only [Mandate.advance,clock,if_pos expired]
  exact ⟨True.intro,True.intro⟩

private theorem material_step (before : Current) (action : Action) (plain : Renewal.material action = true) :
    ((Mandate.law base epoch.scope).step before action).technology = before.technology := by
  unfold RawLaw.step
  split
  · cases operation : action.operation <;> simp_all [RawLaw.paidStep,Renewal.material]
  · rfl

private theorem material_word (before : Current) (index : Nat) (word : List Action)
    (plain : ∀ action ∈ word, Renewal.material action = true) :
    ((Mandate.law base epoch.scope).execute before index word).final.technology = before.technology := by
  induction word generalizing before index with
  | nil => rfl
  | cons action tail ih =>
    change ((Mandate.law base epoch.scope).execute ((Mandate.law base epoch.scope).step before action) (index+1) tail).final.technology = _
    rw [ih _ _ (fun action inside => plain action (List.mem_cons_of_mem _ inside))]
    exact material_step epoch before action (plain action List.mem_cons_self)

private theorem front_material (intent : Intent) (before : Current) (choice : Choice) :
    ∀ action ∈ front epoch intent before choice, Renewal.material action = true := by
  rcases choice with ⟨actor,method⟩
  cases intent <;> cases method <;>
    simp only [front,pairFront,Future.provision,Future.funding]
  all_goals (try split_ifs) <;> simp [Renewal.material,Exit.production]

theorem every_admission_grant_has_the_selected_actor (before : Current) (choice : Choice)
    (grant : Grant base epoch.scope before (candidate epoch .admission before choice)) :
    grant.candidate = choice.actor := by
  have inside : grant.acceptance.item.val.request ∈ candidate epoch .admission before choice := by
    have mapped : grant.acceptance.item.val.request ∈
        ((Mandate.law base epoch.scope).rawItems before (candidate epoch .admission before choice)).map ExecutionItem.request :=
      List.mem_map.mpr ⟨grant.acceptance.item.val,grant.acceptance.item.property,rfl⟩
    simpa only [RawLaw.rawItems,RawLaw.inventory_requests_exact] using mapped
  change grant.acceptance.item.val.request ∈ front epoch .admission before choice ++
    [request epoch.scope (commandBefore epoch .admission before choice) (sponsor epoch) (.propose choice.actor),
      request epoch.scope (acceptanceBefore epoch before choice) choice.actor .accept,signature epoch choice.actor] at inside
  rcases List.mem_append.mp inside with material | commands
  · have plain := front_material epoch .admission before choice _ material
    rw [Renewal.material,grant.acceptance.operation] at plain
    cases plain
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at commands
    rcases commands with proposal | acceptance | signature
    · have operation := grant.acceptance.operation
      rw [proposal] at operation
      have marked := grant.acceptance.marked
      rw [← (Operation.revise.inj operation).2,Mandate.advance_last,grant.accepted_kind] at marked
      cases marked
    · exact grant.candidate_actually_signed.symm.trans (congrArg Request.signer acceptance)
    · have operation := grant.acceptance.operation
      rw [signature] at operation
      cases operation

theorem front_keeps_the_original_authority (intent : Intent) (before : Current) (choice : Choice) :
    (commandBefore epoch intent before choice).technology = before.technology :=
  material_word epoch before 0 _ (front_material epoch intent before choice)

theorem paid_exit_is_the_original_holders_own_action (before : Current) (paid : Paid epoch .exit before) :
    before.technology.holder = some paid.choice.actor := by
  have owned := (paid_exit_retires_the_actual_holder epoch before paid).1
  rw [front_keeps_the_original_authority] at owned
  exact owned

theorem paid_exit_keeps_all_pre_exit_claims (before : Current) (paid : Paid epoch .exit before) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .exit before paid.choice)).final.claims =
      (commandBefore epoch .exit before paid.choice).claims := by
  have valid := paid.legal.2 _ (exit_item_is_actual epoch before paid.choice)
  rw [command_final]
  simp only [commands,RawLaw.execute,signature_step]
  exact (Mandate.paid_command_effect base epoch.scope _ _ .exit valid).2

theorem paid_renewal_is_the_same_holders_fresh_command (before : Current) (paid : Paid epoch .renewal before) :
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .renewal before paid.choice)).final.technology.holder = before.technology.holder ∧
    ((Mandate.law base epoch.scope).execute before 0 (candidate epoch .renewal before paid.choice)).final.technology.last = some .renew := by
  let first := commandBefore epoch .renewal before paid.choice
  let middle := (Mandate.law base epoch.scope).step first (request epoch.scope first (sponsor epoch) (.propose paid.choice.actor))
  have actual : (⟨(front epoch .renewal before paid.choice).length + 1,middle,
      request epoch.scope middle paid.choice.actor .renew⟩ : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit) ∈
      (Mandate.law base epoch.scope).rawItems before (candidate epoch .renewal before paid.choice) := by
    rw [command_items]
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have accepted := paid.legal.2 _ actual
  have effect := Mandate.paid_command_effect base epoch.scope _ _ .renew accepted
  rw [command_final]
  simp only [commands,RawLaw.execute,signature_step]
  change ((Mandate.law base epoch.scope).step middle (request epoch.scope middle paid.choice.actor .renew)).technology.holder = _ ∧
    ((Mandate.law base epoch.scope).step middle (request epoch.scope middle paid.choice.actor .renew)).technology.last = _
  rw [effect.1,Mandate.advance_last]
  constructor
  · change middle.technology.holder = before.technology.holder
    have kept : middle.technology.holder = first.technology.holder := by
      dsimp only [middle,RawLaw.step]
      split <;> rfl
    exact kept.trans (congrArg State.holder (front_keeps_the_original_authority epoch .renewal before paid.choice))
  · rfl

variable {epoch} (inventory : Inventory epoch)

theorem paid_admission_adds_an_actual_native_grant
    (paid : Paid epoch .admission (current epoch inventory.inputs))
    (selected : choose epoch .admission (current epoch inventory.inputs) = some paid) :
    inventory.grants.length < (staged inventory .admission).grants.length := by
  have actual := paid_admission_has_an_original_grant epoch _ paid
  have newborn : 0 < (Mandate.Challenge.Cross.newbornGrants epoch.bound (inputs := inventory.inputs) (emit inventory .admission)).length := by
    unfold Mandate.Challenge.Cross.newbornGrants
    simp only [List.length_map,List.length_attach]
    change 0 < (grantsAt base epoch.scope
      (World.actual inventory (emit inventory .admission)).before
      (World.actual inventory (emit inventory .admission)).submitted).length
    rw [(World.actual_word_and_cut inventory (emit inventory .admission)).1,
      (World.actual_word_and_cut inventory (emit inventory .admission)).2]
    rw [emit,paid_word_is_the_actual_selected_candidate epoch _ _ paid selected]
    exact List.length_pos_iff.mpr (by intro nil; rw [nil] at actual; cases actual)
  change inventory.grants.length <
    (inventory.grants.map (fun record => record.advance epoch.bound (emit inventory .admission)) ++
      Mandate.Challenge.Cross.newbornGrants epoch.bound (inputs := inventory.inputs) (emit inventory .admission)).length
  simp only [List.length_append,List.length_map]
  omega

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
