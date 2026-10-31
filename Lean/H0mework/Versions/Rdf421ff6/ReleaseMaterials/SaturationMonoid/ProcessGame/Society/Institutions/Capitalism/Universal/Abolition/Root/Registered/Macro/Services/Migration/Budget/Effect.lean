import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {source : OutstandingSource Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {current : Physical.Cursor Party Good Port Technology Instrument}
  {code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
  {start : RawCurrent Party Good Technology Instrument}
  {candidates : List (Material.Migration.CodePair Party Good Port Technology Instrument)}

namespace CompletedAt

variable (answer : CompletedAt source depth count prefixLimit renewalLimit current code start candidates)

def afterFees : RawCurrent Party Good Technology Instrument :=
  match answer with
  | .selected _ payment _ _ => payment.microNext
  | .exhausted (before := before) _ => before
  | .blocked (before := before) _ _ _ => before

def paidCount : Nat :=
  match answer with
  | .selected (paidCount := paidCount) _ _ _ _ => paidCount + 1
  | .exhausted (paidCount := paidCount) _ => paidCount
  | .blocked (paidCount := paidCount) _ _ _ => paidCount

def payments : Review.PaidMicroRun source.seed.law code.request start answer.afterFees answer.paidCount :=
  match answer with
  | .selected prior payment _ _ => .snoc prior.payments payment
  | .exhausted prior => prior.payments
  | .blocked prior _ _ => prior.payments

def feeWord := List.replicate answer.paidCount code.request

def selectedPair : Option (Material.Migration.CodePair Party Good Port Technology Instrument) :=
  match answer with
  | .selected (pair := pair) _ _ _ _ => some pair
  | .exhausted .. | .blocked .. => none

def lastRequests : RawEvent Party Good Port Technology Instrument :=
  match answer with
  | .selected (pair := pair) .. => pair.1
  | .exhausted .. => []
  | .blocked .. => [code.request]

def requests : RawEvent Party Good Port Technology Instrument := answer.feeWord ++ answer.lastRequests

/-- Fee steps retain their micro-clock. Only the selected front advances
the period, using duration at the actual fee-paid current. -/
def effect : RawCurrent Party Good Technology Instrument :=
  match answer.selectedPair with
  | some pair => source.seed.law.next answer.afterFees pair.1
  | none => answer.afterFees

theorem actual_fee_balance :
    answer.afterFees.stock code.scope.payer code.scope.good + (answer.paidCount : ℚ) * code.scope.amount =
      start.stock code.scope.payer code.scope.good := answer.payments.material_balance code.scope

theorem physical_review_budget :
    answer.paidCount ≤ Review.physicalBudget code.request code.scope start :=
  answer.payments.count_le_original_budget code.scope

theorem candidate_inventory_budget : answer.paidCount ≤ candidates.length := by
  cases answer with
  | selected prior payment checked generated =>
      have inventory := prior.inventory_exact
      simp only [List.length_cons] at inventory
      simp only [paidCount]
      omega
  | exhausted prior =>
      have inventory := prior.inventory_exact
      simp only [List.length_nil, add_zero] at inventory
      exact Nat.le_of_eq inventory
  | blocked prior obstruction generated =>
      have inventory := prior.inventory_exact
      simp only [List.length_cons] at inventory
      simp only [paidCount]
      omega

theorem fees_preserve_original_claims : answer.afterFees.claims = start.claims :=
  answer.payments.original_claims_unchanged code.scope

theorem fees_preserve_original_technology : answer.afterFees.technology = start.technology := by
  have all : ∀ {before after : RawCurrent Party Good Technology Instrument} {size : Nat},
      Review.PaidMicroRun source.seed.law code.request before after size → after.technology = before.technology := by
    intro before after size run
    induction run with
    | nil => rfl
    | snoc prior payment previous =>
        rename_i middle paidCount
        have same : payment.microNext.technology = middle.technology := by
          simp only [Review.PaymentAt.microNext, RawLaw.step, if_pos payment.accepted,
            RawLaw.paidStep, code.scope.operation]
        exact same.trans previous
  exact all answer.payments

theorem fees_do_not_invent_a_period :
    answer.afterFees.clock = start.clock ∧ answer.afterFees.round = start.round := answer.payments.same_period

theorem fee_execution_reaches_the_same_current (index : Nat) :
    (source.seed.law.execute start index answer.feeWord).final = answer.afterFees :=
  answer.payments.execution_is_the_original_fee_word index

theorem selected_pair_retains_its_post_payment_checks
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
    (selected : answer.selectedPair = some pair) :
    Checks source depth count prefixLimit renewalLimit current code answer.paidCount answer.afterFees pair := by
  cases answer with
  | selected prior payment checked generated =>
      simp only [selectedPair, Option.some.injEq] at selected
      subst pair
      exact checked
  | exhausted prior => cases selected
  | blocked prior obstruction generated => cases selected

theorem selected_front_uses_the_real_post_fee_clock
    (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
    (selected : answer.selectedPair = some pair) :
    answer.effect.clock = start.clock + max 0 (source.seed.law.duration answer.afterFees) ∧
      answer.effect.round = start.round + 1 := by
  rw [effect, selected]
  change answer.afterFees.clock + _ = _ ∧ answer.afterFees.round + 1 = _
  rw [answer.fees_do_not_invent_a_period.1, answer.fees_do_not_invent_a_period.2]
  exact ⟨rfl, rfl⟩

theorem obstruction_keeps_the_paid_current (notSelected : answer.selectedPair = none) :
    answer.effect = answer.afterFees := by rw [effect, notSelected]

theorem material_effect_is_the_original_interpreter :
    answer.effect.stock = (source.seed.law.execute start 0 answer.requests).final.stock ∧
      answer.effect.claims = (source.seed.law.execute start 0 answer.requests).final.claims ∧
      answer.effect.technology = (source.seed.law.execute start 0 answer.requests).final.technology := by
  have run := answer.payments
  cases answer with
  | selected prior payment checked generated =>
      simp only [requests, feeWord, lastRequests, effect, selectedPair, source.seed.law.execute_append]
      rw [run.execution_is_the_original_fee_word 0]
      simp only [afterFees]
      rw [Review.execution_final_independent_of_index source.seed.law payment.microNext _ _ 0]
      exact ⟨rfl, rfl, rfl⟩
  | exhausted prior =>
      simp only [requests, feeWord, lastRequests, effect, selectedPair, List.append_nil]
      rw [run.execution_is_the_original_fee_word 0]
      exact ⟨rfl, rfl, rfl⟩
  | blocked prior obstruction generated =>
      simp only [requests, feeWord, lastRequests, effect, selectedPair, source.seed.law.execute_append]
      rw [run.execution_is_the_original_fee_word 0]
      simp only [afterFees, RawLaw.execute, obstruction.actual_source_preserves_current]
      simp

theorem complete_material_balance (person : Party) (good : Good) :
    answer.effect.stock person good + source.seed.law.totalDebit (source.seed.law.rawItems start answer.requests) person good =
      start.stock person good + source.seed.law.totalCredit (source.seed.law.rawItems start answer.requests) person good := by
  rw [answer.material_effect_is_the_original_interpreter.1]
  exact source.seed.law.execute_material_balance start 0 answer.requests person good

end CompletedAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.CompletedAt.complete_material_balance
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.CompletedAt.selected_front_uses_the_real_post_fee_clock
