import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source

/-! Production and the actual debt response preserve physical exit supplies.
No material is inserted into the raw current by a certificate. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Ready bound inputs)

def materialTotal (before : Current) (good : Good) := before.stock false good + before.stock true good

private theorem located_total (actor : Bool) (goods : Bundle Good) (good : Good) :
    flowAt (locate actor goods) false good + flowAt (locate actor goods) true good = amount Good goods good := by
  cases actor <;> simp [flowAt,locate,amount,List.map_map,Function.comp_def]

private theorem paid_total (before : Current) (action : Action)
    (valid : (law fresh).Valid before action) (good : Good) :
    materialTotal ((law fresh).step before action) good = materialTotal before good -
      (flowAt ((law fresh).debit before action) false good + flowAt ((law fresh).debit before action) true good) +
      (flowAt ((law fresh).credit before action) false good + flowAt ((law fresh).credit before action) true good) := by
  rw [RawLaw.step,if_pos valid]
  dsimp only [materialTotal,RawLaw.paidStep]
  ring

def ResponseOperation (action : Action) : Prop :=
  match action.operation with
  | .produce _ | .transfer _ _ _ | .settle _ _ _ _ => True
  | _ => False

theorem execute_material_healthy (before : Current) (word : List Action) (index : Nat)
    (healthy : MaterialHealthy before) : MaterialHealthy ((law fresh).execute before index word).final := by
  induction word generalizing before index with
  | nil => exact healthy
  | cons action tail ih => exact ih _ _ ((law fresh).step_stock_nonnegative before action healthy)

theorem response_step_preserves_exit_material (before : Current) (action : Action)
    (healthy : MaterialHealthy before) (available : ExitEnvelope before) (response : ResponseOperation action) :
    ExitEnvelope ((law fresh).step before action) := by
  by_cases valid : (law fresh).Valid before action
  · cases operation : action.operation with
    | produce actor =>
        have balance := paid_total fresh before action valid .service
        have debit : (law fresh).debit before action = locate actor [(.feedstock,1)] := by
          simp [law,Mandate.law,RawLaw.debit,operation,base]
        have credit : (law fresh).credit before action = locate actor [(.service,3)] := by
          simp [law,Mandate.law,RawLaw.credit,operation,base]
        rw [debit,credit,located_total,located_total] at balance
        norm_num [amount] at balance
        rw [if_neg (by decide : Good.feedstock ≠ Good.service),sub_zero] at balance
        change 1 ≤ materialTotal ((law fresh).step before action) .service ∨ _
        apply Or.inl
        have nonnegative : 0 ≤ materialTotal before .service := add_nonneg (healthy false .service) (healthy true .service)
        linarith
    | transfer sender recipient goods =>
        have same : ∀ good, materialTotal ((law fresh).step before action) good = materialTotal before good := by
          intro good
          have balance := paid_total fresh before action valid good
          simpa only [RawLaw.debit,RawLaw.credit,operation,located_total,sub_add_cancel] using balance
        change 1 ≤ materialTotal ((law fresh).step before action) .service ∨ 1 ≤ materialTotal ((law fresh).step before action) .feedstock
        rw [same,same]
        exact available
    | settle instrument debtor creditor quantity =>
        have same : ∀ good, materialTotal ((law fresh).step before action) good = materialTotal before good := by
          intro good
          have balance := paid_total fresh before action valid good
          simpa only [RawLaw.debit,RawLaw.credit,operation,located_total,sub_add_cancel] using balance
        change 1 ≤ materialTotal ((law fresh).step before action) .service ∨ 1 ≤ materialTotal ((law fresh).step before action) .feedstock
        rw [same,same]
        exact available
    | use actor goods purpose => simp only [ResponseOperation,operation] at response
    | issue instrument issuer creditor quantity => simp only [ResponseOperation,operation] at response
    | assign instrument issuer sender recipient quantity => simp only [ResponseOperation,operation] at response
    | revise actor target => simp only [ResponseOperation,operation] at response
    | present => simp only [ResponseOperation,operation] at response
  · rw [(law fresh).rejected_preserves_current before action valid]
    exact available

theorem response_word_preserves_exit_material (before : Current) (word : List Action) (index : Nat)
    (healthy : MaterialHealthy before) (available : ExitEnvelope before)
    (response : ∀ action ∈ word, ResponseOperation action) :
    ExitEnvelope ((law fresh).execute before index word).final := by
  induction word generalizing before index with
  | nil => exact available
  | cons action tail ih =>
      exact ih _ _ ((law fresh).step_stock_nonnegative before action healthy)
        (response_step_preserves_exit_material fresh before action healthy available (response action List.mem_cons_self))
        (fun item member => response item (List.mem_cons_of_mem _ member))

private theorem repayment_candidate_is_response (before : Current) (position : Repayment.Position Bool Unit) :
    ∀ action ∈ Repayment.candidate (law fresh) position before, ResponseOperation action := by
  intro action member
  simp only [Repayment.candidate,List.mem_append,Repayment.preparation] at member
  rcases member with front | payment
  · split at front
    · exact False.elim (List.not_mem_nil front)
    · cases List.mem_singleton.mp front
      trivial
  · cases List.mem_singleton.mp payment
    trivial

private theorem repair_is_response (before : Current) (position : Repayment.Position Bool Unit) :
    ∀ action ∈ Repayment.Portfolio.Repair.word (law fresh) position before, ResponseOperation action := by
  intro action member
  unfold Repayment.Portfolio.Repair.word at member
  split at member
  · exact False.elim (List.not_mem_nil member)
  · exact repayment_candidate_is_response fresh before position action member
  · rcases List.mem_append.mp member with candidate | repair
    · exact repayment_candidate_is_response fresh before position action candidate
    · obtain ⟨order,_,rfl⟩ := List.mem_map.mp repair
      trivial

theorem portfolio_preserves_exit_material (before : Current) (positions : List (Repayment.Position Bool Unit))
    (healthy : MaterialHealthy before) (available : ExitEnvelope before) :
    ExitEnvelope ((law fresh).next before (Repayment.Portfolio.word (law fresh) positions before)) := by
  change ExitEnvelope ((law fresh).execute before 0 (Repayment.Portfolio.word (law fresh) positions before)).final
  induction positions generalizing before with
  | nil => exact available
  | cons position tail ih =>
      rw [Repayment.Portfolio.word,Repayment.Portfolio.execute_append_final]
      exact ih _ (execute_material_healthy fresh _ _ _ healthy)
        (response_word_preserves_exit_material fresh _ _ _ healthy available (repair_is_response fresh before position))


def reserveSupply (before : Current) : List Action :=
  let missing := 1 - (reserveStart fresh before).stock fresh.actor .feedstock
  if 0 < missing then
    [⟨!fresh.actor,[],.resource,[],.transfer (!fresh.actor) fresh.actor [(.feedstock,missing)]⟩]
  else []

def reservePrefix (before : Current) := financedFront fresh before ++ reserveSupply fresh before

def reserveProduction (before : Current) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(reservePrefix fresh before).length,((law fresh).execute before 0 (reservePrefix fresh before)).final,
    Exit.production fresh.actor⟩

private theorem reserve_front_decomposition (before : Current) :
    Method.reserved.front fresh before = reservePrefix fresh before ++ [Exit.production fresh.actor] := by
  simp only [Method.front,reserveFront,reservePrefix,reserveSupply,Future.provision,List.append_assoc]

private theorem item_prefix (before : Current) (left right : List Action)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ (law fresh).rawItems before left) :
    item ∈ (law fresh).rawItems before (left ++ right) := by
  unfold RawLaw.rawItems
  rw [(law fresh).execute_append]
  exact List.mem_append_left _ member

theorem reserve_production_is_in_the_actual_candidate (before : Current) :
    reserveProduction fresh before ∈ (law fresh).rawItems before (candidate fresh before .reserved) := by
  have front : reserveProduction fresh before ∈ (law fresh).rawItems before (Method.reserved.front fresh before) := by
    rw [reserve_front_decomposition]
    unfold RawLaw.rawItems
    rw [(law fresh).execute_append]
    apply List.mem_append_right
    simp only [RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false,zero_add]
    rfl
  unfold candidate
  apply item_prefix fresh
  unfold serviceWord
  exact item_prefix fresh _ _ _ _
    (item_prefix fresh _ _ _ _ (item_prefix fresh _ _ _ _ (item_prefix fresh _ _ _ _ front)))

private theorem production_adds_three_service (before : Current) (actor : Bool)
    (valid : (law fresh).Valid before (Exit.production actor)) :
    ((law fresh).step before (Exit.production actor)).stock actor .service = before.stock actor .service + 3 := by
  rw [RawLaw.step,if_pos valid]
  cases actor <;> simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,Mandate.law,base,
    Exit.production,locate,flowAt,amount]

theorem selected_reserved_word_really_produces_its_extra_service (before : Current) (paid : Paid fresh before)
    (selected : select fresh before = some paid) (reserved : paid.method = .reserved) :
    reserveProduction fresh before ∈ (law fresh).rawItems before (emitAt fresh before) ∧
    (law fresh).Valid (reserveProduction fresh before).before (reserveProduction fresh before).request ∧
    ((law fresh).step (reserveProduction fresh before).before (reserveProduction fresh before).request).stock fresh.actor .service =
      (reserveProduction fresh before).before.stock fresh.actor .service + 3 ∧
    ((law fresh).step (reserveProduction fresh before).before (reserveProduction fresh before).request).claims =
      (reserveProduction fresh before).before.claims := by
  have member := reserve_production_is_in_the_actual_candidate fresh before
  have legal : (law fresh).Valid (reserveProduction fresh before).before (reserveProduction fresh before).request := by
    apply paid.pass.1
    rw [reserved]
    exact member
  refine ⟨?_,legal,production_adds_three_service fresh _ _ legal,?_⟩
  · simpa only [emitAt,selected,Option.map_some,Option.getD_some,reserved] using member
  · rw [RawLaw.step,if_pos legal]
    rfl

theorem every_legal_candidate_generates_its_own_exit_material (before : Current) (method : Method)
    (healthy : MaterialHealthy before)
    (legal : ∀ item ∈ (law fresh).rawItems before (candidate fresh before method),
      (law fresh).Valid item.before item.request) :
    ExitEnvelope ((law fresh).next before (candidate fresh before method)) := by
  let word := serviceWord fresh before method
  let middle := ((law fresh).execute before 0 word).final
  by_cases enough : ExitEnvelope middle
  · change ExitEnvelope ((law fresh).execute before 0 (word ++ restoreExit fresh middle)).final
    rw [restoreExit,if_pos enough,List.append_nil]
    exact enough
  · let supply : List Action :=
      if 0 < 1-middle.stock fresh.actor .feedstock then
        [⟨!fresh.actor,[],.resource,[],.transfer (!fresh.actor) fresh.actor
          [(.feedstock,1-middle.stock fresh.actor .feedstock)]⟩]
      else []
    let restorationPrefix := word ++ supply
    let item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
      ⟨restorationPrefix.length,((law fresh).execute before 0 restorationPrefix).final,Exit.production fresh.actor⟩
    have emitted : candidate fresh before method = restorationPrefix ++ [Exit.production fresh.actor] := by
      simp only [candidate,restoreExit,if_neg enough,Future.provision,restorationPrefix,supply,word,middle,List.append_assoc]
    have inside : item ∈ (law fresh).rawItems before (candidate fresh before method) := by
      rw [emitted]
      unfold RawLaw.rawItems
      rw [(law fresh).execute_append]
      apply List.mem_append_right
      simp only [RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false,zero_add]
      rfl
    have accepted := legal item inside
    have nonnegative := execute_material_healthy fresh before restorationPrefix 0 healthy
    have balance := paid_total fresh item.before item.request accepted .service
    have debit : (law fresh).debit item.before item.request = locate fresh.actor [(.feedstock,1)] := by
      simp [item,Exit.production,RawLaw.debit,law,Mandate.law,base]
    have credit : (law fresh).credit item.before item.request = locate fresh.actor [(.service,3)] := by
      simp [item,Exit.production,RawLaw.credit,law,Mandate.law,base]
    rw [debit,credit,located_total,located_total] at balance
    norm_num [amount] at balance
    rw [if_neg (by decide : Good.feedstock ≠ Good.service),sub_zero] at balance
    have supplyNonnegative : 0 ≤ materialTotal item.before .service :=
      add_nonneg (nonnegative false .service) (nonnegative true .service)
    have result : ExitEnvelope ((law fresh).step item.before item.request) := by
      apply Or.inl
      change 1 ≤ materialTotal ((law fresh).step item.before item.request) .service
      linarith
    change ExitEnvelope ((law fresh).execute before 0 (candidate fresh before method)).final
    rw [emitted,Repayment.Portfolio.execute_append_final]
    exact result

theorem selected_word_preserves_exit_material (before : Current) (payment : Paid fresh before)
    (selected : select fresh before = some payment) :
    ExitEnvelope ((law fresh).next before (emitAt fresh before)) := by
  have actual := every_legal_candidate_generates_its_own_exit_material fresh before payment.method
    payment.pass.2.2.2 payment.pass.1
  simpa only [emitAt,selected,Option.map_some,Option.getD_some] using actual

theorem selected_actual_service_and_response_preserve_exit_material
    (payment : Paid fresh (start fresh)) (selected : select fresh (start fresh) = some payment) :
    MaterialHealthy (current fresh 4) ∧ ExitEnvelope (current fresh 4) := by
  have first := (actual fresh 1).after_exact
  have same : (actual fresh 1).after = afterService fresh := by
    change OutstandingSource.History.currentAt (source fresh) (epochInputs fresh) 3 =
      OutstandingSource.History.currentAt (source fresh) (firstInputs fresh) 3
    rw [(OutstandingSource.History.actual_frame _ _ _).1,
      (OutstandingSource.History.actual_frame _ _ _).1]
    exact congrArg (fun past => past.frame.raw)
      (OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
        (source fresh) (firstInputs fresh) [responseWord fresh] 3 (by simp [firstInputs]))
  rw [same] at first
  change afterService fresh = (law fresh).next (actual fresh 1).before (actual fresh 1).submitted at first
  rw [first_word_uses_the_actual_start,first_word_is_actually_emitted] at first
  have healthy : MaterialHealthy (afterService fresh) := by
    rw [first]
    exact execute_material_healthy fresh _ _ 0 payment.pass.2.2.2
  have available : ExitEnvelope (afterService fresh) := by
    rw [first]
    exact selected_word_preserves_exit_material fresh _ payment selected
  have second := (actual fresh 2).after_exact
  change current fresh 4 = (law fresh).next (actual fresh 2).before (actual fresh 2).submitted at second
  rw [response_uses_the_actual_first_after,response_is_the_actual_second_word] at second
  rw [second]
  exact ⟨execute_material_healthy fresh _ _ 0 healthy,
    portfolio_preserves_exit_material fresh _ _ healthy available⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
