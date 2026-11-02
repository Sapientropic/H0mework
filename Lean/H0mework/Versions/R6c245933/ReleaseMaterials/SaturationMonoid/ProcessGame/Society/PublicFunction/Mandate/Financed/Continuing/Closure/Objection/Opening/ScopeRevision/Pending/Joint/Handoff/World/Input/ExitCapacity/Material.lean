import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Effects
/-! Exact material exit envelope for the source-owned two-party law.
The obstruction covers every finite raw word, including refused requests. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable (epoch : Epoch)

def total (before : Current) (good : Good) := before.stock false good + before.stock true good

def Envelope (before : Current) : Prop := 1 ≤ total before .service ∨ 1 ≤ total before .feedstock
instance (before : Current) : Decidable (Envelope before) := by unfold Envelope total; infer_instance

theorem production_valid (before : Current) (actor : Bool) :
    (Mandate.law base epoch.scope).Valid before (Exit.production actor) ↔ 1 ≤ before.stock actor .feedstock := by
  simp [Mandate.law,Exit.production,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    eraseCurrent,eraseRequest,eraseOperation,TaskUse,base,Epoch.scope,Handoff.Ready.scope,
    NonnegativeBundle,locate,flowAt,amount]

theorem exit_valid (before : Current) (actor : Bool) (holder : before.technology.holder = some actor) :
    (Mandate.law base epoch.scope).Valid before (request epoch.scope before actor .exit) ↔ 1 ≤ before.stock actor .service := by
  simp [Mandate.law,request,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    Mandate.CanRun,Mandate.advance,base,Epoch.scope,Handoff.Ready.scope,NonnegativeBundle,
    locate,flowAt,amount,holder]

private theorem signature_valid (before : Current) (actor : Bool) (holder : before.technology.holder = some actor) :
    (Mandate.law base epoch.scope).Valid before (Input.signature epoch actor) := by
  simp [Mandate.law,Input.signature,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    eraseCurrent,eraseRequest,eraseOperation,TaskUse,base,Epoch.scope,Handoff.Ready.scope,
    NonnegativeBundle,locate,flowAt,amount,holder]

def transfer (actor : Bool) (good : Good) (quantity : ℚ) : Action :=
  ⟨!actor,[],.resource,[],.transfer (!actor) actor [(good,quantity)]⟩

private theorem transfer_valid (before : Current) (actor : Bool) (good : Good) (quantity : ℚ) :
    (Mandate.law base epoch.scope).Valid before (transfer actor good quantity) ↔
      0 ≤ quantity ∧ quantity ≤ before.stock (!actor) good := by
  cases actor <;> cases good <;>
    simp [Mandate.law,transfer,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
      RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
      eraseCurrent,eraseRequest,eraseOperation,TaskUse,base,Epoch.scope,Handoff.Ready.scope,
      NonnegativeBundle,locate,flowAt,amount]

def issue (actor : Bool) (quantity : ℚ) : Action :=
  ⟨actor,[],.resource,[],.issue () actor (!actor) quantity⟩

private theorem issue_valid (before : Current) (actor : Bool) (quantity : ℚ) :
    (Mandate.law base epoch.scope).Valid before (issue actor quantity) ↔ 0 ≤ quantity := by
  simp [Mandate.law,issue,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    eraseCurrent,eraseRequest,eraseOperation,TaskUse,base,Epoch.scope,Handoff.Ready.scope,
    NonnegativeBundle,locate,flowAt,amount]

private theorem transfer_stock (before : Current) (actor : Bool) (good : Good) (quantity : ℚ)
    (valid : (Mandate.law base epoch.scope).Valid before (transfer actor good quantity)) :
    ((Mandate.law base epoch.scope).step before (transfer actor good quantity)).stock actor good =
      before.stock actor good + quantity := by
  rw [RawLaw.step,if_pos valid]
  cases actor <;> cases good <;>
    simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,transfer,locate,flowAt,amount]

private theorem productive_stock (before : Current) (actor : Bool)
    (valid : (Mandate.law base epoch.scope).Valid before (Exit.production actor)) :
    ((Mandate.law base epoch.scope).step before (Exit.production actor)).stock actor .service =
      before.stock actor .service + 3 := by
  rw [RawLaw.step,if_pos valid]
  cases actor <;>
    simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,Mandate.law,base,Exit.production,locate,flowAt,amount]

private theorem issue_stock (before : Current) (actor : Bool) (quantity : ℚ) :
    ((Mandate.law base epoch.scope).step before (issue actor quantity)).stock = before.stock := by
  funext party good
  unfold RawLaw.step
  split <;> simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,issue,flowAt,amount]

private theorem material_technology (before : Current) (actor : Bool) (good : Good) (quantity : ℚ) :
    ((Mandate.law base epoch.scope).step before (transfer actor good quantity)).technology = before.technology ∧
    ((Mandate.law base epoch.scope).step before (Exit.production actor)).technology = before.technology ∧
    ((Mandate.law base epoch.scope).step before (issue actor quantity)).technology = before.technology := by
  constructor
  · unfold RawLaw.step; split <;> rfl
  constructor <;> (unfold RawLaw.step; split <;> rfl)

private theorem direct_legal (before : Current) (actor : Bool) (holder : before.technology.holder = some actor)
    (enough : 1 ≤ before.stock actor .service) : Input.Legal epoch .exit before ⟨actor,.direct⟩ := by
  refine ⟨?_,?_⟩
  · simp only [Eligible,holder,Option.isSome_some]
  · intro item inside
    have sigstep : (Mandate.law base epoch.scope).step before (Input.signature epoch actor) = before :=
      (Mandate.law base epoch.scope).presentation_preserves_material_and_claims before _ rfl
    simp only [candidate,front,commands,List.nil_append,RawLaw.rawItems,RawLaw.execute,sigstep,
      List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl
    · exact signature_valid epoch before actor holder
    · exact (exit_valid epoch before actor holder).mpr enough

private theorem legal_of_front (before : Current) (actor : Bool) (method : Method)
    (holder : before.technology.holder = some actor)
    (valid : ∀ item ∈ (Mandate.law base epoch.scope).rawItems before (front epoch .exit before ⟨actor,method⟩),
      (Mandate.law base epoch.scope).Valid item.before item.request)
    (enough : 1 ≤ (commandBefore epoch .exit before ⟨actor,method⟩).stock actor .service) :
    Input.Legal epoch .exit before ⟨actor,method⟩ := by
  refine ⟨by simp only [Eligible,holder,Option.isSome_some],?_⟩
  intro item inside
  unfold candidate RawLaw.rawItems at inside
  rw [(Mandate.law base epoch.scope).execute_append] at inside
  rcases List.mem_append.mp inside with earlier | later
  · exact valid item earlier
  · have kept : (commandBefore epoch .exit before ⟨actor,method⟩).technology.holder = some actor := by
      rw [front_keeps_the_original_authority,holder]
    have sigstep : (Mandate.law base epoch.scope).step (commandBefore epoch .exit before ⟨actor,method⟩)
        (Input.signature epoch actor) = commandBefore epoch .exit before ⟨actor,method⟩ :=
      (Mandate.law base epoch.scope).presentation_preserves_material_and_claims _ _ rfl
    change item ∈ ((Mandate.law base epoch.scope).execute (commandBefore epoch .exit before ⟨actor,method⟩)
      (0+(front epoch .exit before ⟨actor,method⟩).length) _).items at later
    simp only [commands,RawLaw.execute,sigstep,List.mem_cons,List.not_mem_nil,or_false] at later
    rcases later with rfl | rfl
    · exact signature_valid epoch _ actor kept
    · exact (exit_valid epoch _ actor kept).mpr enough

private theorem total_actor (before : Current) (actor : Bool) (good : Good) :
    total before good = before.stock actor good + before.stock (!actor) good := by
  cases actor
  · rfl
  · exact add_comm _ _

private theorem financed_legal (before : Current) (actor : Bool) (holder : before.technology.holder = some actor)
    (low : before.stock actor .service < 1) (enough : 1 ≤ total before .service) :
    Input.Legal epoch .exit before ⟨actor,.financed⟩ := by
  have positive : 0 < 1-before.stock actor .service := sub_pos.mpr low
  have supply : 1-before.stock actor .service ≤ before.stock (!actor) .service := by
    rw [total_actor before actor .service] at enough
    linarith
  have issued := (issue_valid epoch before actor (1-before.stock actor .service)).mpr (le_of_lt positive)
  let middle := (Mandate.law base epoch.scope).step before (issue actor (1-before.stock actor .service))
  have sent : (Mandate.law base epoch.scope).Valid middle (transfer actor .service (1-before.stock actor .service)) := by
    apply (transfer_valid epoch middle actor .service _).mpr
    rw [show middle.stock = before.stock from issue_stock epoch before actor _]
    exact ⟨le_of_lt positive,supply⟩
  have shape : front epoch .exit before ⟨actor,.financed⟩ =
      [issue actor (1-before.stock actor .service),transfer actor .service (1-before.stock actor .service)] := by
    simp only [front,Future.funding,if_pos positive]
    rfl
  apply legal_of_front epoch before actor .financed holder
  · rw [shape]
    intro item inside
    simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl
    · exact issued
    · exact sent
  · unfold commandBefore
    rw [shape]
    change 1 ≤ ((Mandate.law base epoch.scope).step middle (transfer actor .service (1-before.stock actor .service))).stock actor .service
    rw [transfer_stock epoch middle actor .service _ sent,show middle.stock = before.stock from issue_stock epoch before actor _]
    linarith

private theorem transfer_other_stock (before : Current) (actor : Bool) (quantity : ℚ) (good other : Good)
    (different : good ≠ other) :
    ((Mandate.law base epoch.scope).step before (transfer actor good quantity)).stock actor other = before.stock actor other := by
  unfold RawLaw.step
  split
  · simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,transfer,locate,flowAt,amount,different]
  · rfl

private theorem supplied_legal (before : Current) (actor : Bool) (holder : before.technology.holder = some actor)
    (nonnegative : 0 ≤ before.stock actor .service) (enough : 1 ≤ total before .feedstock) :
    Input.Legal epoch .exit before ⟨actor,.supplied⟩ := by
  by_cases missing : 0 < 1-before.stock actor .feedstock
  · have supply : 1-before.stock actor .feedstock ≤ before.stock (!actor) .feedstock := by
      rw [total_actor before actor .feedstock] at enough
      linarith
    have sent := (transfer_valid epoch before actor .feedstock (1-before.stock actor .feedstock)).mpr ⟨le_of_lt missing,supply⟩
    let middle := (Mandate.law base epoch.scope).step before (transfer actor .feedstock (1-before.stock actor .feedstock))
    have feed : 1 ≤ middle.stock actor .feedstock := by
      rw [show middle.stock actor .feedstock = _ from transfer_stock epoch before actor .feedstock _ sent]
      linarith
    have produced := (production_valid epoch middle actor).mpr feed
    have shape : front epoch .exit before ⟨actor,.supplied⟩ =
        [transfer actor .feedstock (1-before.stock actor .feedstock),Exit.production actor] := by
      simp only [front,Future.provision,if_pos missing,List.cons_append,List.nil_append]
      rfl
    apply legal_of_front epoch before actor .supplied holder
    · rw [shape]
      intro item inside
      simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl
      · exact sent
      · exact produced
    · unfold commandBefore
      rw [shape]
      change 1 ≤ ((Mandate.law base epoch.scope).step middle (Exit.production actor)).stock actor .service
      rw [productive_stock epoch middle actor produced]
      have same : middle.stock actor .service = before.stock actor .service := transfer_other_stock epoch before actor _ _ _ (by decide)
      rw [same]
      linarith
  · have feed : 1 ≤ before.stock actor .feedstock := by linarith
    have produced := (production_valid epoch before actor).mpr feed
    have shape : front epoch .exit before ⟨actor,.supplied⟩ = [Exit.production actor] := by
      simp only [front,Future.provision,if_neg missing,List.nil_append]
    apply legal_of_front epoch before actor .supplied holder
    · rw [shape]
      intro item inside
      simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl
      exact produced
    · unfold commandBefore
      rw [shape]
      change 1 ≤ ((Mandate.law base epoch.scope).step before (Exit.production actor)).stock actor .service
      rw [productive_stock epoch before actor produced]
      linarith

private theorem listed_legal_exit_generates_payment (before : Current) (choice : Choice)
    (listed : choice ∈ Input.menu epoch .exit before) (valid : Input.Legal epoch .exit before choice) :
    (Input.choose epoch .exit before).isSome = true := by
  cases found : Input.choose epoch .exit before with
  | some payment => rfl
  | none => exact False.elim (Input.no_selected_choice_has_escaped_its_actual_check epoch .exit before found choice listed valid)

theorem source_material_envelope_generates_a_real_exit (before : Current) (actor : Bool)
    (holder : before.technology.holder = some actor) (nonnegative : 0 ≤ before.stock actor .service)
    (available : Envelope before) : (Input.choose epoch .exit before).isSome = true := by
  have listed (method : Method) : (⟨actor,method⟩ : Choice) ∈ Input.menu epoch .exit before := by
    cases method <;> simp [Input.menu,actors,holder]
  rcases available with service | feedstock
  · by_cases enough : 1 ≤ before.stock actor .service
    · exact listed_legal_exit_generates_payment epoch before ⟨actor,.direct⟩ (listed .direct) (direct_legal epoch before actor holder enough)
    · exact listed_legal_exit_generates_payment epoch before ⟨actor,.financed⟩ (listed .financed)
        (financed_legal epoch before actor holder (lt_of_not_ge enough) service)
  · exact listed_legal_exit_generates_payment epoch before ⟨actor,.supplied⟩ (listed .supplied)
      (supplied_legal epoch before actor holder nonnegative feedstock)

private theorem located_total (actor : Bool) (goods : Bundle Good) (good : Good) :
    flowAt (locate actor goods) false good + flowAt (locate actor goods) true good = amount Good goods good := by
  cases actor <;> simp [flowAt,locate,amount,List.map_map,Function.comp_def]

def Nonnegative (before : Current) : Prop := ∀ actor good, 0 ≤ before.stock actor good

private theorem stock_le_total (before : Current) (nonnegative : Nonnegative before) (actor : Bool) (good : Good) :
    before.stock actor good ≤ total before good := by
  rw [total_actor before actor good]
  exact le_add_of_nonneg_right (nonnegative (!actor) good)

private theorem paid_total_balance (before : Current) (action : Action)
    (valid : (Mandate.law base epoch.scope).Valid before action) (good : Good) :
    total ((Mandate.law base epoch.scope).step before action) good = total before good -
      (flowAt ((Mandate.law base epoch.scope).debit before action) false good +
        flowAt ((Mandate.law base epoch.scope).debit before action) true good) +
      (flowAt ((Mandate.law base epoch.scope).credit before action) false good +
        flowAt ((Mandate.law base epoch.scope).credit before action) true good) := by
  rw [RawLaw.step,if_pos valid]
  dsimp only [total,RawLaw.paidStep]
  ring

private theorem below_envelope_preserved_by_every_raw_step (before : Current) (action : Action)
    (nonnegative : Nonnegative before) (unavailable : ¬ Envelope before) :
    ¬ Envelope ((Mandate.law base epoch.scope).step before action) := by
  have cold : total before .service < 1 ∧ total before .feedstock < 1 := by
    simpa only [Envelope,not_or,not_le] using unavailable
  by_cases accepted : (Mandate.law base epoch.scope).Valid before action
  · have balance := paid_total_balance epoch before action accepted
    cases kind : action.operation with
    | produce actor =>
        have enough : 1 ≤ before.stock actor .feedstock := by
          have paid := (Mandate.law base epoch.scope).debit_affordable before action nonnegative accepted actor .feedstock
          simpa [RawLaw.debit,kind,Mandate.law,base,locate,flowAt,amount] using paid
        exact False.elim (not_le_of_gt cold.2 (enough.trans (stock_le_total before nonnegative actor .feedstock)))
    | transfer sender recipient goods =>
        have same (good : Good) : total ((Mandate.law base epoch.scope).step before action) good = total before good := by
          have equation := balance good
          simp only [RawLaw.debit,RawLaw.credit,kind,located_total] at equation
          linarith
        simpa only [Envelope,same] using unavailable
    | settle code debtor creditor quantity =>
        have same (good : Good) : total ((Mandate.law base epoch.scope).step before action) good = total before good := by
          have equation := balance good
          simp only [RawLaw.debit,RawLaw.credit,kind,located_total] at equation
          linarith
        simpa only [Envelope,same] using unavailable
    | use bearer goods purpose =>
        have decreases (good : Good) : total ((Mandate.law base epoch.scope).step before action) good ≤ total before good := by
          have positive := amount_nonnegative ((Mandate.law base epoch.scope).debit before action) accepted.2.2.2.1
          have first := positive (false,good)
          have second := positive (true,good)
          have equation := balance good
          have zeroCredit : (Mandate.law base epoch.scope).credit before action = [] := by simp only [RawLaw.credit,kind]
          rw [zeroCredit] at equation
          rw [show flowAt ([] : Flow Bool Good) false good = 0 from rfl,
            show flowAt ([] : Flow Bool Good) true good = 0 from rfl,zero_add] at equation
          change 0 ≤ flowAt ((Mandate.law base epoch.scope).debit before action) false good at first
          change 0 ≤ flowAt ((Mandate.law base epoch.scope).debit before action) true good at second
          linarith
        exact fun available => available.elim
          (fun enough => not_le_of_gt cold.1 (enough.trans (decreases .service)))
          (fun enough => not_le_of_gt cold.2 (enough.trans (decreases .feedstock)))
    | revise actor target =>
        have enough : 1 ≤ before.stock actor .service := by
          have paid := (Mandate.law base epoch.scope).debit_affordable before action nonnegative accepted actor .service
          simpa [RawLaw.debit,kind,Mandate.law,Epoch.scope,Handoff.Ready.scope,locate,flowAt,amount] using paid
        exact False.elim (not_le_of_gt cold.1 (enough.trans (stock_le_total before nonnegative actor .service)))
    | issue code debtor creditor quantity | assign code debtor sender recipient quantity | present =>
        have same (good : Good) : total ((Mandate.law base epoch.scope).step before action) good = total before good := by
          have equation := balance good
          simpa [RawLaw.debit,RawLaw.credit,kind,flowAt,amount] using equation
        simpa only [Envelope,same] using unavailable
  · rw [(Mandate.law base epoch.scope).rejected_preserves_current before action accepted]
    exact unavailable

theorem below_envelope_preserved_by_every_raw_word (before : Current) (word : List Action) (index : Nat)
    (nonnegative : Nonnegative before) (unavailable : ¬ Envelope before) :
    Nonnegative ((Mandate.law base epoch.scope).execute before index word).final ∧
    ¬ Envelope ((Mandate.law base epoch.scope).execute before index word).final := by
  induction word generalizing before index with
  | nil => exact ⟨nonnegative,unavailable⟩
  | cons action tail ih =>
      exact ih ((Mandate.law base epoch.scope).step before action) (index+1)
        ((Mandate.law base epoch.scope).step_stock_nonnegative before action nonnegative)
        (below_envelope_preserved_by_every_raw_step epoch before action nonnegative unavailable)

theorem below_envelope_forbids_every_later_exit (before : Current) (word : List Action)
    (nonnegative : Nonnegative before) (unavailable : ¬ Envelope before) (actor : Bool) :
    let after := ((Mandate.law base epoch.scope).execute before 0 word).final
    ¬ (Mandate.law base epoch.scope).Valid after (request epoch.scope after actor .exit) := by
  dsimp only
  intro valid
  let after := ((Mandate.law base epoch.scope).execute before 0 word).final
  have still := below_envelope_preserved_by_every_raw_word epoch before word 0 nonnegative unavailable
  have totalLow : total after .service < 1 := (not_or.mp still.2).1 |> lt_of_not_ge
  have paid := (Mandate.law base epoch.scope).debit_affordable after (request epoch.scope after actor .exit) still.1 valid actor .service
  have enough : 1 ≤ after.stock actor .service := by
    simpa [RawLaw.debit,request,Mandate.law,Epoch.scope,Handoff.Ready.scope,locate,flowAt,amount] using paid
  exact not_le_of_gt totalLow (enough.trans (stock_le_total after still.1 actor .service))

theorem source_envelope_is_complete_for_all_finite_exit_continuations (before : Current) (actor : Bool)
    (nonnegative : Nonnegative before) (holder : before.technology.holder = some actor) :
    Envelope before ↔ ∃ word : List Action,
      (∀ item ∈ (Mandate.law base epoch.scope).rawItems before word, (Mandate.law base epoch.scope).Valid item.before item.request) ∧
      (Mandate.law base epoch.scope).Valid ((Mandate.law base epoch.scope).execute before 0 word).final
        (request epoch.scope ((Mandate.law base epoch.scope).execute before 0 word).final actor .exit) := by
  constructor
  · intro available
    have present := source_material_envelope_generates_a_real_exit epoch before actor holder (nonnegative actor .service) available
    let paid := (Input.choose epoch .exit before).get present
    refine ⟨front epoch .exit before paid.choice,?_,?_⟩
    · intro item inside
      apply paid.legal.2 item
      unfold candidate RawLaw.rawItems
      rw [(Mandate.law base epoch.scope).execute_append]
      exact List.mem_append_left _ inside
    · have own := paid_exit_is_the_original_holders_own_action epoch before paid
      have same : paid.choice.actor = actor := Option.some.inj (own.symm.trans holder)
      have actual := paid.legal.2 _ (exit_item_is_actual epoch before paid.choice)
      change (Mandate.law base epoch.scope).Valid (commandBefore epoch .exit before paid.choice)
        (request epoch.scope (commandBefore epoch .exit before paid.choice) paid.choice.actor .exit) at actual
      rw [same] at actual
      exact actual
  · rintro ⟨word,legal,possible⟩
    by_contra absent
    exact below_envelope_forbids_every_later_exit epoch before word nonnegative absent actor possible

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity
