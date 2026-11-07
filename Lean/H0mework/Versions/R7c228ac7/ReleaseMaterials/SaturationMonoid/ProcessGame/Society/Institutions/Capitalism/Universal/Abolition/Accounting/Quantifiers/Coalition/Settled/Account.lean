import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled.Word

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled

open Source.Program Innovation Priority
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

/-- Read actual delivered uses on the same original inventory. These are
spent resources, not an independently minted welfare balance. -/
def consumedAt (law : RawLaw Party Good Port Technology Instrument)
    [DecidableEq Instrument] (item : ExecutionItem Party Good Port Technology Instrument) :
    Profit.Vector (Party := Party) (Good := Good) :=
  match item.request.operation with
  | .use .. => Financial.flowVector (law.actualDebit item.before item.request)
  | _ => 0

def consumed (law : RawLaw Party Good Port Technology Instrument)
    [DecidableEq Instrument] (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Profit.Vector (Party := Party) (Good := Good) := (items.map (consumedAt law)).sum

variable [DecidableEq Instrument]

private theorem the_original_step_balances_spending_exactly
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (noTake : ¬ Policy.CompulsoryTake item.request.operation)
    (noFinance : ¬ Policy.FinancialOperation item.request.operation) :
    Financial.fullChange law item.before item.request + consumedAt law item = 0 := by
  cases operation : item.request.operation <;>
    simp_all [Policy.CompulsoryTake,Policy.FinancialOperation]
  all_goals
    by_cases valid : law.Valid item.before item.request <;>
      simp [Financial.fullChange,Financial.materialChange,Financial.claimChange,Financial.rawClaimChange,
        consumedAt,RawLaw.actualCredit,RawLaw.actualDebit,RawLaw.credit,RawLaw.debit,operation,valid,
        Financial.flowVector]

theorem the_complete_inventory_balances_the_same_actual_uses
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (noTake : ∀ item ∈ items, ¬ Policy.CompulsoryTake item.request.operation)
    (noFinance : ∀ item ∈ items, ¬ Policy.FinancialOperation item.request.operation) :
    Profit.fullIncome law items + consumed law items = 0 := by
  induction items with
  | nil => simp [Profit.fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,consumed]
  | cons item rest inherited =>
    have first := the_original_step_balances_spending_exactly law item
      (noTake _ List.mem_cons_self) (noFinance _ List.mem_cons_self)
    have later := inherited (fun next member => noTake next (List.mem_cons_of_mem _ member))
      (fun next member => noFinance next (List.mem_cons_of_mem _ member))
    simp only [Profit.fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,consumed,
      List.map_cons,List.sum_cons,map_add] at later ⊢
    simp only [Financial.fullChange] at first
    ext key
    have one := congrArg (fun effect : Profit.Vector (Party := Party) (Good := Good) => effect key) first
    have two := congrArg (fun effect : Profit.Vector (Party := Party) (Good := Good) => effect key) later
    simp only [Finsupp.add_apply,Finsupp.zero_apply] at one two ⊢
    linarith

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

theorem every_coalition_has_zero_unbacked_income_on_the_paid_original_row
    (claim : Responsibility.Family.Claim source past nature response)
    (state : Responsibility.Family.State claim)
    (law : RawLaw Party Good Port Technology Instrument) (actors : List Party)
    (proposal : RawEvent Party Good Port Technology Instrument)
    (paid : Responsibility.Family.State.isPaid claim state)
    (members : Party → Bool) (good : Good) :
    let items := law.rawItems state.raw (Policy.evaluate claim state law actors proposal).executableWord
    read members good (Profit.fullIncome law items) + read members good (consumed law items) = 0 := by
  let evaluation := Policy.evaluate claim state law actors proposal
  have original (item : ExecutionItem Party Good Port Technology Instrument)
      (member : item ∈ law.rawItems state.raw evaluation.executableWord) :
      item.request ∈ evaluation.executableWord := by
    rw [← law.inventory_requests_exact state.raw 0 evaluation.executableWord]
    exact List.mem_map.mpr ⟨item,member,rfl⟩
  have balanced := the_complete_inventory_balances_the_same_actual_uses law
    (law.rawItems state.raw evaluation.executableWord)
    (fun item member => Policy.accepted_paid_prefix_has_no_new_compulsory_request claim state law actors
      paid evaluation.accepted item.request (original item member))
    (fun item member => Policy.accepted_prefix_has_no_financial_operation claim state law actors
      evaluation.accepted item.request (original item member))
  simpa only [map_add,map_zero] using congrArg (read members good) balanced

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled
