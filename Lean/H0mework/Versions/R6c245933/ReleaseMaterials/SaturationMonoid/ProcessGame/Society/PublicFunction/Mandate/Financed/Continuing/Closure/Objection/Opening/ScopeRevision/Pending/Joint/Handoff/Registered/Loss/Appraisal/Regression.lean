import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Regression
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

def price : Original.Prices .service where
  rate := fun good => if good = .service then 1 else 0
  normalized := rfl
  nonnegative := by intro good; split <;> norm_num
  slot := fun _ _ _ => 0
  event := fun _ _ _ => 0
  time := fun _ => 0
  time_nonnegative := fun _ => le_refl 0
  holder := fun _ _ => 0
  offer := fun _ _ => 0
  standing := fun _ _ => 0
  eligible := fun _ _ => 0
  method := fun _ _ _ _ => 0
  exitMaterial := fun _ => 0
  paid := fun _ => 0
  version := fun _ => 0
  last := fun _ _ => 0

open Loss.Regression in
 theorem actual_compensation_changes_the_two_original_legs_but_not_the_gross_loss :
    (rawValues price cursor.book false false).sum = 3 ∧
    (rawValues price cursor.book true false).sum = 0 ∧
    (rawValues price afterPayment.book false false).sum = 0 ∧
    (rawValues price afterPayment.book true false).sum = 3 ∧
    rawValue price cursor.book false = 3 ∧ rawValue price afterPayment.book false = 3 := by
  have literal : Loss.accept cursor.book (law fresh) cursor.before cursor.word =
      Loss.allocate cursor.book (law fresh) cursor.before := if_pos rfl
  have actual : afterPayment.book = Loss.allocate cursor.book (law fresh) cursor.before ++
      [Entry.ofVisit (visit cursor.state cursor.word)] :=
    congrArg (fun book => book ++ [Entry.ofVisit (visit cursor.state cursor.word)]) literal
  have beforeRemaining : (rawValues price cursor.book false false).sum = 3 := by with_unfolding_all decide +kernel
  have beforePaid : (rawValues price cursor.book true false).sum = 0 := by with_unfolding_all decide +kernel
  have afterRemaining : (rawValues price afterPayment.book false false).sum = 0 := by
    rw [actual,Loss.allocate,the_source_selects_the_original_loss_cell]
    with_unfolding_all decide +kernel
  have afterPaid : (rawValues price afterPayment.book true false).sum = 3 := by
    rw [actual,Loss.allocate,the_source_selects_the_original_loss_cell]
    with_unfolding_all decide +kernel
  refine ⟨beforeRemaining,beforePaid,afterRemaining,afterPaid,?_,?_⟩
  · simp only [rawValue,beforeRemaining,beforePaid,add_zero]
  · simp only [rawValue,afterRemaining,afterPaid,zero_add]

abbrev authority := Registered.Regression.authority
abbrev inventory := Registered.Regression.inventory
abbrev fresh := Registered.Regression.fresh

 theorem the_source_menu_really_contains_a_self_executable_paid_window :
    personal authority inventory fresh false ∈ menu authority inventory fresh ∧
      sameWindow authority inventory fresh 0 false (personal authority inventory fresh false)
        (personal authority inventory fresh false) = true := by
  have available : Appraisal.Available authority inventory fresh false (personal authority inventory fresh false) := by
    unfold Appraisal.Available Registered.Legal
    with_unfolding_all decide +kernel
  have paid : (Registered.assess authority inventory fresh (personal authority inventory fresh false)).isPaid = true := by
    with_unfolding_all decide +kernel
  refine ⟨List.mem_append_left _ List.mem_cons_self,?_⟩
  simp only [sameWindow,paidWindow,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨⟨⟨available,paid⟩,paid⟩,True.intro⟩

 theorem actual_settlement_horizon_can_follow_the_original_paid_service_window :
    (source fresh).seed.task.deadline <
      (Registered.final authority inventory fresh (personal authority inventory fresh false)).clock := by
  with_unfolding_all decide +kernel

private theorem value_at_declared_price (word : List Action) :
    value authority inventory fresh 0 price word false =
      -rawValue price (Loss.cursorAt authority inventory fresh word 0).book false := by
  simp [value,slotValues,eventValues,agencyValue,timeCost,price,
    World.Input.Event.SelfDeviation.Comparison.Appraisal.agencyScore]

private theorem terminal_quote (word : List Action) (good : Good) :
    Finance.quotedAfter authority inventory fresh word 0 false good =
      Registered.Finance.quotedAfter authority inventory fresh word false good := by
  unfold Finance.quotedAfter Registered.Finance.quotedAfter
  have same : (Loss.cursorAt authority inventory fresh word 0).before = Registered.final authority inventory fresh word :=
    (Loss.initial authority inventory fresh word).before_is_the_same_actual_current
  rw [same]
  rfl

 theorem the_personal_service_has_a_real_cost_against_the_captured_history :
    payoff authority inventory fresh 0 price (personal authority inventory fresh false) false <
      payoff authority inventory fresh 0 price Registered.Regression.word false := by
  unfold payoff
  rw [value_at_declared_price,value_at_declared_price]
  erw [the_financial_sum_is_the_original_actual_net_change authority inventory fresh 0 price Registered.Regression.word false,
    the_financial_sum_is_the_original_actual_net_change authority inventory fresh 0 price (personal authority inventory fresh false) false]
  simp only [terminal_quote]
  with_unfolding_all decide +kernel

 theorem the_personal_service_is_an_actual_same_window_alternative :
    sameWindow authority inventory fresh 0 false Registered.Regression.word
      (personal authority inventory fresh false) = true := by
  have available := (every_checked_window_has_its_own_actual_payment_cut_and_signature _ _ _ _ _ _ _
    the_source_menu_really_contains_a_self_executable_paid_window.2).1
  have basePaid : (Registered.assess authority inventory fresh Registered.Regression.word).isPaid = true :=
    Registered.Regression.the_registered_word_and_original_alternative_are_both_consumed_as_paid.1
  have newPaid := (every_checked_window_has_its_own_actual_payment_cut_and_signature _ _ _ _ _ _ _
    the_source_menu_really_contains_a_self_executable_paid_window.2).2.2.1
  have window : sameWindow authority inventory fresh 0 false Registered.Regression.word
      (personal authority inventory fresh false) = true := by
    simp only [sameWindow,paidWindow,Bool.and_eq_true_iff,decide_eq_true_eq]
    refine ⟨⟨⟨available,basePaid⟩,(Registered.actual_paid_is_checked_not_supplied _ _ _ _).mpr newPaid⟩,?_⟩
    have left : (Loss.cursorAt authority inventory fresh Registered.Regression.word 0).before =
        Registered.final authority inventory fresh Registered.Regression.word :=
      (Loss.initial authority inventory fresh Registered.Regression.word).before_is_the_same_actual_current
    have right : (Loss.cursorAt authority inventory fresh (personal authority inventory fresh false) 0).before =
        Registered.final authority inventory fresh (personal authority inventory fresh false) :=
      (Loss.initial authority inventory fresh (personal authority inventory fresh false)).before_is_the_same_actual_current
    rw [left,right]
    with_unfolding_all decide +kernel
  exact window

 theorem the_source_computes_stability_on_the_actual_personal_domain :
    stable authority inventory fresh 0 price false Registered.Regression.word = true := by
  have notBetter : ¬ payoff authority inventory fresh 0 price Registered.Regression.word false <
      payoff authority inventory fresh 0 price (personal authority inventory fresh false) false :=
    not_lt_of_ge (le_of_lt the_personal_service_has_a_real_cost_against_the_captured_history)
  have rejected : (sameWindow authority inventory fresh 0 false Registered.Regression.word
      (personal authority inventory fresh false) &&
      decide (payoff authority inventory fresh 0 price Registered.Regression.word false <
        payoff authority inventory fresh 0 price (personal authority inventory fresh false) false)) = false := by
    simp only [decide_eq_false notBetter,Bool.and_false]
  simp only [stable,improvements,menu,List.filter_append,List.filter_cons,rejected]
  with_unfolding_all decide +kernel

 theorem the_actual_stable_source_consumes_the_complete_cost_bound :
    financial authority inventory fresh 0 price Registered.Regression.word false true -
      financial authority inventory fresh 0 price (personal authority inventory fresh false) false true ≤
      budget authority inventory fresh 0 price Registered.Regression.word false (personal authority inventory fresh false) -
        gains authority inventory fresh 0 price Registered.Regression.word false (personal authority inventory fresh false) :=
  computed_stability_bounds_the_original_selected_net authority inventory fresh 0 price false Registered.Regression.word
    the_source_computes_stability_on_the_actual_personal_domain _
    the_source_menu_really_contains_a_self_executable_paid_window.1 the_personal_service_is_an_actual_same_window_alternative

 theorem the_paid_external_signature_is_not_the_bearers_executable_word :
    ¬ Appraisal.Available authority inventory fresh false Registered.Regression.word := by
  intro checked
  have control := checked.2
  have denied : ¬ World.Input.Event.SelfDeviation.LocalWord false Registered.Regression.word := by
    with_unfolding_all decide +kernel
  exact denied control

 theorem a_paid_lookalike_cannot_pass_the_self_execution_gate (baseline : List Action) (count : Nat) :
    sameWindow authority inventory fresh count false baseline Registered.Regression.word = false := by
  cases window : sameWindow authority inventory fresh count false baseline Registered.Regression.word with
  | false => rfl
  | true => exact (the_paid_external_signature_is_not_the_bearers_executable_word
      (every_checked_window_has_its_own_actual_payment_cut_and_signature _ _ _ _ _ _ _ window).1).elim

 theorem the_empty_override_is_not_a_paid_baseline :
    paidWindow authority inventory fresh [] = false := by
  have empty : (Registered.assess authority inventory fresh []).isPaid = false :=
    Registered.Regression.explicit_empty_input_and_payment_without_service_do_not_forge_public_payment.1
  simp only [paidWindow,empty]
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Regression
