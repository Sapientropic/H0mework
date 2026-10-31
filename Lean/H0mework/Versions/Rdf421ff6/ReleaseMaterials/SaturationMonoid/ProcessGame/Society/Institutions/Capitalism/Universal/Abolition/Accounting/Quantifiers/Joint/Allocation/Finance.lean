import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

/-- Cash paid on an original financial claim retires that claim; it is not
a second payment of either physical repair obligation. -/
theorem pure_financial_items_cannot_discharge_either_physical_row
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (financial : ¬ Responsibility.NonFinancialOperation item.request.operation)
    (pKey : Party × Good) (gKey : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    productiveTransfer seed old p work item pKey = 0 ∧
      productiveNet seed p item pKey = 0 ∧ grossTransfer seed old p g work item gKey = 0 := by
  cases operation : item.request.operation <;>
    simp_all [Responsibility.NonFinancialOperation,productiveTransfer,productiveNet,grossTransfer,Kernel.reservation,Kernel.net,Kernel.gross]

theorem financial_items_leave_both_allocations_literal
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (financial : ¬ Responsibility.NonFinancialOperation item.request.operation) :
    (afterItem seed old p g work item).netProductive = work.netProductive ∧
      (afterItem seed old p g work item).gross = work.gross := by
  constructor
  · funext key
    have zero := pure_financial_items_cannot_discharge_either_physical_row seed old p g work item financial key
      (key.1,key.1,key.2)
    have creditZero : productiveCredit seed old p g work item key = 0 := by
      cases operation : item.request.operation <;>
        simp_all [Responsibility.NonFinancialOperation,productiveCredit,Kernel.productiveCredit]
    exact (show work.netProductive key + productiveNet seed p item key +
        productiveCredit seed old p g work item key = work.netProductive key by rw [creditZero,zero.2.1]; simp)
  · funext key
    have zero := pure_financial_items_cannot_discharge_either_physical_row seed old p g work item financial
      (key.1,key.2.2) key
    change max 0 (work.gross key - grossTransfer seed old p g work item key) = work.gross key
    rw [zero.2.2,sub_zero,max_eq_right (work.gross_nonnegative key)]

theorem a_financial_inventory_keeps_both_allocations_literal
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (financial : ∀ item ∈ items, ¬ Responsibility.NonFinancialOperation item.request.operation) :
    (items.foldl (afterItem seed old p g) work).netProductive = work.netProductive ∧
      (items.foldl (afterItem seed old p g) work).gross = work.gross := by
  induction items generalizing work with
  | nil => exact ⟨rfl,rfl⟩
  | cons item tail inherited =>
      have first := financial_items_leave_both_allocations_literal seed old p g work item (financial item List.mem_cons_self)
      have later := inherited (afterItem seed old p g work item)
        (fun next member => financial next (List.mem_cons_of_mem _ member))
      exact ⟨later.1.trans first.1,later.2.trans first.2⟩

theorem a_financial_word_keeps_both_allocations_literal
    (old : Party × Good → ℚ) (p g : Bool)
    (gross : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ) (nonnegative : ∀ key, 0 ≤ gross key)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (financial : ∀ request ∈ word, ¬ Responsibility.NonFinancialOperation request.operation) :
    (run seed old p g gross nonnegative before word).netProductive = (fun _ => 0) ∧
      (run seed old p g gross nonnegative before word).gross = gross := by
  apply a_financial_inventory_keeps_both_allocations_literal
  intro item original
  apply financial item.request
  have member := List.mem_map_of_mem (f := ExecutionItem.request) original
  change item.request ∈ ((actualLaw seed).execute before 0 word).items.map ExecutionItem.request at member
  rw [(actualLaw seed).inventory_requests_exact before 0 word] at member
  exact member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
