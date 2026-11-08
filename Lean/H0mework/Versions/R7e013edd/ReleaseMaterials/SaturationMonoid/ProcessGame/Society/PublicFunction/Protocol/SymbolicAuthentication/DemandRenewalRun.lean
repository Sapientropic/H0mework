import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalStep

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalRun
open Institutions.Capitalism.Universal.Source.Program
open RecycledQuorumMaterial (Current Action)
open RenewedQuorumMaterial (law)
open RenewedQuorumSource (fee)
open DemandRenewalStep

structure Report where
  final : Current
  words : List (List Action)
  served : List Bool
  pending : List Bool

def prepend (current : Current) (second : Bool) (tail : Report) : Report :=
  {tail with
    words := DemandRenewalStep.words current second ++ tail.words
    served := second :: tail.served}

def refusal (current : Current) (second : Bool) (tail : List Bool) : Report :=
  ⟨next current second,DemandRenewalStep.words current second,[],second :: tail⟩

def run : List Bool → Current → Report :=
  List.rec (fun current => ⟨current,[],[],[]⟩)
    (fun second tail previous current =>
      if paid current then prepend current second (previous (next current second))
      else refusal current second tail)

theorem run_cons (current : Current) (second : Bool) (tail : List Bool) :
    run (second :: tail) current =
      if paid current then prepend current second (run tail (next current second))
      else refusal current second tail := rfl

inductive PaidTrace : Current → List (List Action) → Prop
  | nil (current : Current) : PaidTrace current []
  | cons (current : Current) (word : List Action) (tail : List (List Action))
      (paid : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request)
      (rest : PaidTrace (law.next current word) tail) : PaidTrace current (word :: tail)

theorem paid_trace_append (current : Current) (left right : List (List Action))
    (first : PaidTrace current left)
    (second : PaidTrace (left.foldl law.next current) right) : PaidTrace current (left ++ right) := by
  induction first with
  | nil => exact second
  | cons current word tail paid rest ih => exact .cons current word _ paid (ih second)

theorem paid_step_generates_its_complete_actual_trace (current : Current) (second : Bool)
    (accepted : paid current = true) : PaidTrace current (DemandRenewalStep.words current second) := by
  obtain ⟨charged,renewed⟩ := a_paid_step_has_only_actual_valid_items current second accepted
  unfold DemandRenewalStep.words
  cases actual : refill current with
  | false =>
    have same : prepared current = current := by simp [prepared,actual]
    exact .cons current [fee second] [] (by simpa only [same] using charged) (.nil _)
  | true =>
    have same : prepared current = law.next current RenewedQuorumMaterial.word := by simp [prepared,actual]
    exact .cons current RenewedQuorumMaterial.word [[fee second]] (renewed actual)
      (.cons _ [fee second] [] (by simpa only [same] using charged) (.nil _))

theorem every_report_keeps_the_literal_actual_source (demands : List Bool) (current : Current) :
    (run demands current).words.foldl law.next current = (run demands current).final ∧
      (run demands current).served ++ (run demands current).pending = demands := by
  induction demands generalizing current with
  | nil => exact ⟨rfl,rfl⟩
  | cons second tail ih =>
    rw [run_cons]
    split
    · rename_i actual
      have rest := ih (next current second)
      simp only [prepend,List.foldl_append,the_generated_words_execute_their_literal_next]
      exact ⟨rest.1,congrArg (List.cons second) rest.2⟩
    · exact ⟨the_generated_words_execute_their_literal_next current second,rfl⟩

theorem the_original_budget_funds_every_demand_in_its_capacity
    (demands : List Bool) (current : Current) (cash fuel : Nat)
    (stock : Inventory current cash fuel) (within : demands.length ≤ cash + 3 * fuel) :
    (run demands current).pending = [] ∧ (run demands current).served = demands ∧
      PaidTrace current (run demands current).words ∧
      ∃ cash' fuel', Inventory (run demands current).final cash' fuel' ∧
        cash' + 3 * fuel' + demands.length = cash + 3 * fuel := by
  induction demands generalizing current cash fuel with
  | nil => exact ⟨rfl,rfl,.nil _,cash,fuel,stock,by simp⟩
  | cons second tail ih =>
    obtain ⟨charged,cash',fuel',nextStock,balance⟩ :=
      actual_resources_generate_a_paid_step_and_the_smaller_budget current cash fuel second stock (by simp only [List.length_cons] at within;omega)
    obtain ⟨empty,served,trace,lastCash,lastFuel,lastStock,total⟩ :=
      ih (next current second) cash' fuel' nextStock (by simp only [List.length_cons] at within;omega)
    rw [run_cons,if_pos charged]
    refine ⟨empty,congrArg (List.cons second) served,?_,lastCash,lastFuel,lastStock,?_⟩
    · apply paid_trace_append current (DemandRenewalStep.words current second)
      · exact paid_step_generates_its_complete_actual_trace current second charged
      · simpa only [the_generated_words_execute_their_literal_next] using trace
    · simp only [List.length_cons]
      omega

theorem every_demand_preserves_the_exact_source_capacity_cut
    (demands : List Bool) (current : Current) (cash fuel : Nat)
    (stock : Inventory current cash fuel) :
    (run demands current).served.length = min demands.length (cash + 3 * fuel) := by
  induction demands generalizing current cash fuel with
  | nil => rfl
  | cons second tail ih =>
    by_cases positive : 0 < cash + 3 * fuel
    · obtain ⟨charged,cash',fuel',nextStock,balance⟩ :=
        actual_resources_generate_a_paid_step_and_the_smaller_budget current cash fuel second stock positive
      have remaining := ih (next current second) cash' fuel' nextStock
      rw [run_cons,if_pos charged]
      change (second :: (run tail (next current second)).served).length = _
      rw [List.length_cons,remaining,List.length_cons]
      omega
    · have zeroCash : cash = 0 := by omega
      have zeroFuel : fuel = 0 := by omega
      subst cash
      subst fuel
      have refused := exhausted_resources_generate_a_real_refusal current stock
      rw [run_cons,if_neg (by simp [refused])]
      rfl

theorem unpaid_tail_keeps_a_paid_prefix_and_its_first_actual_refusal
    (demands : List Bool) (current : Current) (cash fuel : Nat)
    (stock : Inventory current cash fuel) :
    (run demands current).pending = [] ∨
      ∃ front before second tail,
        (run demands current).words = front ++ DemandRenewalStep.words before second ∧
        before = front.foldl law.next current ∧ PaidTrace current front ∧
        Inventory before 0 0 ∧ paid before = false ∧
        (run demands current).pending = second :: tail := by
  induction demands generalizing current cash fuel with
  | nil => exact Or.inl rfl
  | cons second tail ih =>
    by_cases positive : 0 < cash + 3 * fuel
    · obtain ⟨charged,cash',fuel',nextStock,_⟩ :=
        actual_resources_generate_a_paid_step_and_the_smaller_budget current cash fuel second stock positive
      rw [run_cons,if_pos charged]
      rcases ih (next current second) cash' fuel' nextStock with empty | stopped
      · exact Or.inl empty
      · obtain ⟨front,before,head,rest,words,origin,trace,exhausted,unpaid,pending⟩ := stopped
        refine Or.inr ⟨DemandRenewalStep.words current second ++ front,before,head,rest,?_,?_,?_,exhausted,unpaid,pending⟩
        · change DemandRenewalStep.words current second ++ (run tail (next current second)).words = _
          rw [words,List.append_assoc]
        · rw [List.foldl_append,the_generated_words_execute_their_literal_next]
          exact origin
        · apply paid_trace_append current (DemandRenewalStep.words current second)
          · exact paid_step_generates_its_complete_actual_trace current second charged
          · simpa only [the_generated_words_execute_their_literal_next] using trace
    · have zeroCash : cash = 0 := by omega
      have zeroFuel : fuel = 0 := by omega
      subst cash
      subst fuel
      have refused := exhausted_resources_generate_a_real_refusal current stock
      rw [run_cons,if_neg (by simp [refused])]
      exact Or.inr ⟨[],current,second,tail,rfl,rfl,.nil _,stock,refused,rfl⟩

def items : List (List Action) → Current → List (ExecutionItem Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port (Mandate.State Delegation.Funded.Party Bool) Unit) :=
  List.rec (fun _ => [])
    (fun word _ previous current => law.rawItems current word ++ previous (law.next current word))

theorem every_generated_item_is_paid (current : Current) (events : List (List Action))
    (trace : PaidTrace current events) :
    ∀ item ∈ items events current, law.Valid item.before item.request := by
  induction trace with
  | nil => simp [items]
  | cons current word tail paid rest ih =>
    intro item member
    change item ∈ law.rawItems current word ++ items tail (law.next current word) at member
    rcases List.mem_append.mp member with first | later
    · exact paid item first
    · exact ih item later

theorem the_entire_actual_material_ledger_balances
    (current : Current) (events : List (List Action)) (party : Delegation.Funded.Party) (good : Repayment.Recovery.Good) :
    (events.foldl law.next current).stock party good + law.totalDebit (items events current) party good =
      current.stock party good + law.totalCredit (items events current) party good := by
  induction events generalizing current with
  | nil => simp [items,RawLaw.totalDebit,RawLaw.totalCredit]
  | cons word tail ih =>
    have first := law.actual_next_material_balance current word party good
    have later := ih (law.next current word)
    change (tail.foldl law.next (law.next current word)).stock party good +
      law.totalDebit (law.rawItems current word ++ items tail (law.next current word)) party good =
      current.stock party good + law.totalCredit (law.rawItems current word ++ items tail (law.next current word)) party good
    simp only [RawLaw.totalDebit,RawLaw.totalCredit,List.map_append,List.sum_append] at first later ⊢
    linarith

theorem every_resource_step_preserves_all_original_claims (current : Current) (second : Bool) :
    (next current second).claims = current.claims := by
  have feeClaims (before : Current) : (law.next before [fee second]).claims = before.claims := by
    simp only [RawLaw.next,RawLaw.execute,RawLaw.step]
    split <;> rfl
  rw [next,feeClaims]
  cases actual : refill current with
  | false => simp [prepared,actual]
  | true =>
    have inputs := (of_decide_eq_true actual).2
    simp only [prepared,actual,if_true]
    rw [RenewedQuorumMaterial.actual_next current inputs]
    rfl

theorem every_report_preserves_all_original_claims (demands : List Bool) (current : Current) :
    (run demands current).final.claims = current.claims := by
  induction demands generalizing current with
  | nil => rfl
  | cons second tail ih =>
    rw [run_cons]
    split
    · change (run tail (next current second)).final.claims = _
      rw [ih,every_resource_step_preserves_all_original_claims]
    · exact every_resource_step_preserves_all_original_claims current second

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalRun
